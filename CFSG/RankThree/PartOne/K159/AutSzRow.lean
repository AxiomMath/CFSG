module

public import CFSG.RankThree.PartOne.K159.AutSzAbs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.K159.SzAbs

open CFSG CFSG.ABGLocalTools CFSG.RankThree.PartOne

variable {H : Type} [Group H]

theorem mem_normalizer_omegaOne_of_mem {p : ℕ} {P : Subgroup H} {y : H} (hy : y ∈ P) :
    y ∈ Subgroup.normalizer (omegaOne p P : Set H) := by
  have key : ∀ {y : H}, y ∈ P → ∀ {e : H}, e ∈ omegaOne p P → y * e * y⁻¹ ∈ omegaOne p P := by
    intro y hy e he
    refine Subgroup.closure_induction (p := fun e _ => y * e * y⁻¹ ∈ omegaOne p P) ?_ ?_ ?_ ?_ he
    · rintro x ⟨hxK, hxp⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact P.mul_mem (P.mul_mem hy hxK) (P.inv_mem hy)
      · have : (y * x * y⁻¹) ^ p = y * x ^ p * y⁻¹ := by rw [conj_pow]
        rw [this, hxp]
        group
    · simp
    · intro a b _ _ ha hb
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => key hy he, fun he => ?_⟩
  have := key (P.inv_mem hy) he
  simpa [mul_assoc] using this

variable [Finite H]

theorem sz_row {S : Subgroup H} (hS : S.Normal) (hSz : SzSylow ↥S) (hsimple : IsSimpleGroup ↥S)
    (hC : Subgroup.centralizer (S : Set H) = ⊥) {P : Subgroup H} (hP : CFSG.RankThree.PartOne.IsSylowOf 5 P ⊤)
    (hΩel : IsElementaryAbelian 5 (omegaOne 5 P)) (hΩ : Nat.card (omegaOne 5 P) = 25)
    (hord : ∀ g ∈ torusImage (omegaOne 5 P) S, orderOf g ≤ 4) : False := by
  classical
  have := hS
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP' : CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hP
  set E : Subgroup H := omegaOne 5 P with hE
  have hEP : E ≤ P := (Subgroup.closure_le _).2 fun _ hx => hx.1
  have hPp : IsPGroup 5 P := hP.2.1
  set T : Subgroup H := P ⊓ S with hT
  have hTS : T ≤ S := inf_le_right
  have hTP : T ≤ P := inf_le_left
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 5 T S :=
    hP'.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hS])
  have hTcard : Nat.card T = 25 := by
    rw [hTsyl.card_eq, hSz.card, factorization_five]
    norm_num
  obtain ⟨Q, hQ⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hcycQ : IsCyclic ↥(T.subgroupOf S) := by
    have h1 : IsCyclic ↥(Q : Subgroup ↥S) := hSz.cyclic Q
    rwa [hQ] at h1
  have hcycT : IsCyclic ↥T := (Subgroup.subgroupOfEquivOfLe hTS).isCyclic.1 hcycQ
  have hEnT : ¬ E ≤ T := by
    intro hET
    have hEqT : E = T := Subgroup.eq_of_le_of_card_ge hET (by rw [hTcard, hΩ])
    obtain ⟨g, hg⟩ := hcycT.exists_generator
    have hord25 : orderOf g = 25 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg]
      exact hTcard
    have hg5 : (g : H) ^ 5 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (A := E) (g : H) (by rw [hEqT]; exact g.2)
    have hg5' : g ^ 5 = 1 := Subtype.ext (by simpa using hg5)
    have := orderOf_dvd_of_pow_eq_one hg5'
    rw [hord25] at this
    omega
  have hTcomm : ∀ t ∈ T, ∀ e ∈ E, t * e = e * t := by
    intro t ht e he
    have htP : t ∈ P := hTP ht
    have htS : t ∈ S := hTS ht
    have htN : t ∈ Subgroup.normalizer (E : Set H) := mem_normalizer_omegaOne_of_mem htP
    set φ : MulAut E := E.normalizerMonoidHom ⟨t, htN⟩ with hφ
    have hφmem : φ ∈ torusImage E S :=
      Subgroup.mem_map.2 ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 htS, rfl⟩
    have hφ4 : orderOf φ ≤ 4 := hord φ hφmem
    obtain ⟨k, hk⟩ := hPp ⟨t, htP⟩
    have htk : t ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hφk : φ ^ (5 ^ k) = 1 := by
      have h1 : φ ^ (5 ^ k) =
          E.normalizerMonoidHom ((⟨t, htN⟩ : Subgroup.normalizer (E : Set H)) ^ (5 ^ k)) := by
        rw [map_pow]
      have h2 : (⟨t, htN⟩ : Subgroup.normalizer (E : Set H)) ^ (5 ^ k) = 1 :=
        Subtype.ext (by simpa using htk)
      rw [h1, h2, map_one]
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 (orderOf_dvd_of_pow_eq_one hφk)
    have hj0 : j = 0 := by
      by_contra hne
      have : 5 ^ 1 ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hne)
      omega
    have hφ1 : φ = 1 := by
      rw [← orderOf_eq_one_iff, hj, hj0]
      rfl
    have h3 := congrArg (fun ψ : MulAut E => ((ψ ⟨e, he⟩ : E) : H)) hφ1
    have h4 : t * e * t⁻¹ = e := by simpa [hφ] using h3
    calc t * e = t * e * t⁻¹ * t := by group
      _ = e * t := by rw [h4]
  set P' : Subgroup H := T ⊔ E with hP'
  have hP'P : P' ≤ P := sup_le hTP hEP
  have hP'p : IsPGroup 5 P' := hPp.to_le hP'P
  have hTP' : T ≤ P' := le_sup_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP'p
  have hgt : 25 < Nat.card P' := by
    by_contra hle
    push Not at hle
    have : T = P' := Subgroup.eq_of_le_of_card_ge hTP' (by rw [hTcard]; exact hle)
    exact hEnT (this ▸ (le_sup_right : E ≤ T ⊔ E))
  have h125 : 125 ∣ Nat.card P' := by
    rw [hn] at hgt ⊢
    have h3 : 3 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> omega
    have := pow_dvd_pow 5 h3
    simpa using this
  have hcomm : ∀ x ∈ P', ∀ t ∈ T, x * t = t * x := by
    have hle : P' ≤ Subgroup.centralizer (T : Set H) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have : (⟨t, ht⟩ : ↥T) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨t, ht⟩ := by
          let _ := hcycT.commGroup
          exact mul_comm _ _
        exact congrArg Subtype.val this
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact hTcomm t ht x hx
    intro x hx t ht
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) t ht).symm
  exact sz_core hSz hsimple hC hTS hTcard hP'p hTP' h125 hcomm

end CFSG.RankThree.PartOne.K159.SzAbs
