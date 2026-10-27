module

public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.RankThree.LocalRank.DihedralNormalPrimeComplement

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_eq_three {S : Subgroup G} (hS : Sec4.IsHeisThree S) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set G)) = 3 := by
  rw [← CFSG.center_map_subtype_eq_inf_centralizer S,
    Subgroup.card_map_of_injective S.subtype_injective]
  exact hS.1.2.2.2

theorem card_zpowers_sup_eq_nine {S : Subgroup G} (hS : Sec4.IsHeisThree S) {s : G}
    (hs : s ∈ S) (hsZ : s ∉ S ⊓ Subgroup.centralizer (S : Set G)) :
    Subgroup.zpowers s ⊔ (S ⊓ Subgroup.centralizer (S : Set G)) ≤ S ∧
      Nat.card ↥(Subgroup.zpowers s ⊔ (S ⊓ Subgroup.centralizer (S : Set G))) = 9 := by
  let Z := S ⊓ Subgroup.centralizer (S : Set G)
  have hZcard : Nat.card Z = 3 := card_inf_centralizer_eq_three hS
  have hZle : Z ≤ S := inf_le_left
  have hspow : s ^ 3 = 1 := by
    have h : (⟨s, hs⟩ : ↥S) ^ 3 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨s, hs⟩ : ↥S)
      rwa [hS.2.2] at this
    simpa using congrArg Subtype.val h
  have hs1 : s ≠ 1 := by
    intro h
    exact hsZ (by rw [h]; exact Subgroup.one_mem Z)
  have hord : orderOf s = 3 := orderOf_eq_prime hspow hs1
  have hzpowcard : Nat.card (Subgroup.zpowers s) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hdisj : Subgroup.zpowers s ⊓ Z = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers s ⊓ Z) ∣ 3 := by
      rw [← hzpowcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers s ⊓ Z = Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hzpowcard])
      have hle : Subgroup.zpowers s ≤ Z := by rw [← heq]; exact inf_le_right
      exact hsZ (hle (Subgroup.mem_zpowers s))
  have hcomm : ∀ a ∈ Subgroup.zpowers s, ∀ b ∈ Z, Commute a b := by
    intro a ha b hb
    have hbS : b ∈ S := hZle hb
    have hbC : b ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hb).2
    have haS : a ∈ S := Subgroup.zpowers_le.mpr hs ha
    exact Subgroup.mem_centralizer_iff.mp hbC a haS
  refine ⟨?_, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hs) hZle
  · change Nat.card ↥(Subgroup.zpowers s ⊔ Z) = 9
    rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers s) Z hcomm hdisj,
      hzpowcard, hZcard]

theorem le_normalizer_of_card_eq_nine {S B : Subgroup G} (hS : Sec4.IsHeisThree S)
    (hBS : B ≤ S) (hB : Nat.card B = 9) : S ≤ Subgroup.normalizer (B : Set G) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hBS]
  have hcardS : Nat.card ↥S = 27 := hS.2.1
  have hcardB : Nat.card (B.subgroupOf S) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv, hB]
  have hidx : (B.subgroupOf S).index = 3 := by
    have h := (B.subgroupOf S).index_mul_card
    rw [hcardB, hcardS] at h
    omega
  have hmin : (Nat.card ↥S).minFac = 3 := by rw [hcardS]; norm_num
  exact Subgroup.normal_of_index_eq_minFac_card (H := B.subgroupOf S) (by rw [hidx, hmin])

theorem monoidHom_eq_id_or_inv_of_pow_three {A : Type*} [Group A] [IsMulCommutative A]
    (hexp : ∀ a : A, a ^ 3 = 1) (f : A →* A)
    (hf : ∀ a : A, f a = a ∨ f a = a⁻¹) :
    (∀ a, f a = a) ∨ (∀ a, f a = a⁻¹) := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  by_cases h : ∃ s : A, s ≠ 1 ∧ f s = s
  · left
    obtain ⟨s, hs1, hfs⟩ := h
    intro t
    by_contra ht
    have hft : f t = t⁻¹ := by
      rcases hf t with h' | h'
      · exact absurd h' ht
      · exact h'
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact ht (map_one f)
    have hst := hf (s * t)
    rw [map_mul, hfs, hft, mul_inv] at hst
    rcases hst with hst | hst
    · have h1 : t⁻¹ = t := mul_left_cancel hst
      have ht2 : t ^ 2 = 1 := by
        have h2 : t * t = 1 := by
          have := congrArg (fun x => t * x) h1
          rw [mul_inv_cancel] at this
          exact this.symm
        rwa [pow_two]
      have ht3 : t ^ 3 = 1 := hexp t
      have : t = 1 := by
        calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
          _ = 1 := by rw [ht3, ht2, inv_one, mul_one]
      exact ht1 this
    · have h1 : s = s⁻¹ := mul_right_cancel hst
      have hs2 : s ^ 2 = 1 := by
        have h2 : s * s = 1 := by
          have := congrArg (fun x => x * s) h1
          rw [inv_mul_cancel] at this
          exact this
        rwa [pow_two]
      have hs3 : s ^ 3 = 1 := hexp s
      have : s = 1 := by
        calc s = s ^ 3 * (s ^ 2)⁻¹ := by group
          _ = 1 := by rw [hs3, hs2, inv_one, mul_one]
      exact hs1 this
  · right
    intro t
    rcases hf t with h' | h'
    · by_cases ht1 : t = 1
      · subst ht1; simp
      · exact absurd ⟨t, ht1, h'⟩ h
    · exact h'

theorem eq_or_eq_inv_of_mem_zpowers_of_pow_three {H : Type*} [Group H] {a b : H}
    (ha : a ^ 3 = 1) (hb : b ∈ Subgroup.zpowers a) (hb1 : b ≠ 1) :
    b = a ∨ b = a⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hz : a ^ (3 : ℤ) = 1 := by simpa using ha
  have hk' : a ^ (k % 3) = b := by rw [← zpow_eq_zpow_emod k hz]; exact hk
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hge : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  interval_cases h : k % 3
  · exfalso; apply hb1; rw [← hk', zpow_zero]
  · left; rw [← hk', zpow_one]
  · right
    rw [← hk', zpow_two]
    have h3 : a * a * a = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using ha
    have h2 : a * a = a⁻¹ := by
      have := congrArg (fun x => x * a⁻¹) h3
      simpa [mul_assoc] using this
    exact h2

theorem mem_normalizer_sup_zpowers_of_mem_conj {Z : Subgroup G} {g w : G}
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (h : g * w * g⁻¹ ∈ Subgroup.zpowers w ⊔ Z) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers w ⊔ Z : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap : (Subgroup.zpowers w ⊔ Z).map (MulAut.conj g) =
      Subgroup.zpowers (g * w * g⁻¹) ⊔ Z := by
    rw [Subgroup.map_sup]
    congr 1
    · rw [show (Subgroup.zpowers w).map (MulAut.conj g) =
          (Subgroup.zpowers w).map (MulAut.conj g).toMonoidHom from rfl,
        MonoidHom.map_zpowers]
      rw [show (MulAut.conj g).toMonoidHom w = (MulAut.conj g) w from rfl, MulAut.conj_apply]
    · exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := Z) (g := g)).mp hgZ
  rw [hmap]
  have hle : Subgroup.zpowers (g * w * g⁻¹) ⊔ Z ≤ Subgroup.zpowers w ⊔ Z := by
    apply sup_le
    · rwa [Subgroup.zpowers_le]
    · exact le_sup_right
  have hcard : Nat.card ↥(Subgroup.zpowers (g * w * g⁻¹) ⊔ Z) =
      Nat.card ↥(Subgroup.zpowers w ⊔ Z) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

private theorem inv_of_sq_normalizes_aux {S : Subgroup G}
    (hS : Sec4.IsHeisThree S) {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (S : Set G))
    (h1 : ∀ s ∈ S, s ∉ S ⊓ Subgroup.centralizer (S : Set G) →
      γ ∉ Subgroup.normalizer
        ((Subgroup.zpowers s ⊔ (S ⊓ Subgroup.centralizer (S : Set G)) : Subgroup G) : Set G))
    (h2 : ∀ s ∈ S, s ∉ S ⊓ Subgroup.centralizer (S : Set G) →
      γ ^ 2 ∈ Subgroup.normalizer
        ((Subgroup.zpowers s ⊔ (S ⊓ Subgroup.centralizer (S : Set G)) : Subgroup G) : Set G)) :
    ∀ s ∈ S, γ ^ 2 * s * (γ ^ 2)⁻¹ * s ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
  classical
  let Z : Subgroup G := S ⊓ Subgroup.centralizer (S : Set G)
  let Zc : Subgroup ↥S := Subgroup.center ↥S
  let Q := ↥S ⧸ Zc
  haveI : Zc.Normal := inferInstance
  have hZeq : Z = Zc.map S.subtype := (CFSG.center_map_subtype_eq_inf_centralizer S).symm
  have hSexp : ∀ t : ↥S, t ^ 3 = 1 := by
    intro t
    have := Monoid.pow_exponent_eq_one t
    rwa [hS.2.2] at this
  have hγZ : γ ∈ Subgroup.normalizer (Z : Set G) :=
    CFSG.RankThree.LocalRank.normalizer_le_normalizer_inf_centralizer S hγ
  have hγ2S : γ ^ 2 ∈ Subgroup.normalizer (S : Set G) := pow_mem hγ 2
  have hγ2Z : γ ^ 2 ∈ Subgroup.normalizer (Z : Set G) := pow_mem hγZ 2
  have hcommQ : IsMulCommutative Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Zc)).mpr (by
      rw [hS.1.2.1])
  let Φ : MulAut ↥S := S.normalizerMonoidHom ⟨γ ^ 2, hγ2S⟩
  have hΦmem : ∀ t : ↥S, (Φ t : G) = γ ^ 2 * (t : G) * (γ ^ 2)⁻¹ := by
    intro t
    have := Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨γ ^ 2, hγ2S⟩ t
    simpa [Φ] using this
  have hΦ : Zc.map Φ.toMonoidHom = Zc := Subgroup.map_center_eq Φ
  let α : Q →* Q := QuotientGroup.map Zc Zc Φ.toMonoidHom (by
    intro z hz
    rw [← hΦ]
    exact Subgroup.mem_map_of_mem _ hz)
  have hαmk : ∀ t : ↥S, α (QuotientGroup.mk t) = QuotientGroup.mk (Φ t) :=
    fun t => QuotientGroup.map_mk Zc Zc Φ.toMonoidHom _ t
  have hexpQ : ∀ a : Q, a ^ 3 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | _ t =>
      rw [← QuotientGroup.mk_pow (N := Zc), hSexp t, QuotientGroup.mk_one]
  have hα : ∀ a : Q, α a = a ∨ α a = a⁻¹ := by
    intro a
    induction a using QuotientGroup.induction_on with
    | _ t =>
      by_cases htZc : t ∈ Zc
      · have hΦtZc : Φ t ∈ Zc := by
          rw [← hΦ]
          exact Subgroup.mem_map_of_mem Φ.toMonoidHom htZc
        have h1t : (QuotientGroup.mk t : Q) = 1 := (QuotientGroup.eq_one_iff t).mpr htZc
        have h1Φ : (QuotientGroup.mk (Φ t) : Q) = 1 := (QuotientGroup.eq_one_iff (Φ t)).mpr hΦtZc
        rw [hαmk, h1Φ, h1t, inv_one]
        exact Or.inl rfl
      · have htS : (t : G) ∈ S := t.2
        have htZ : (t : G) ∉ Z := by
          rw [hZeq]
          intro hmem
          obtain ⟨c, hc, hcv⟩ := Subgroup.mem_map.mp hmem
          exact htZc (by
            rw [show t = c from Subtype.ext hcv.symm]
            exact hc)
        have hΦtB : (Φ t : G) ∈ Subgroup.zpowers (t : G) ⊔ Z := by
          have hmem := (Subgroup.mem_normalizer_iff.mp (h2 (t : G) htS htZ) (t : G)).mp
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers (t : G)))
          simpa [hΦmem t] using hmem
        have hΦtZ : (Φ t : G) ∉ Z := by
          intro hmem
          have hinv : (γ ^ 2)⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ hγ2Z
          have hconj : (γ ^ 2)⁻¹ * (Φ t : G) * (γ ^ 2) ∈ Z := by
            simpa using (Subgroup.mem_normalizer_iff.mp hinv (Φ t : G)).mp hmem
          have ht_eq : (t : G) = (γ ^ 2)⁻¹ * (Φ t : G) * (γ ^ 2) := by
            rw [hΦmem t]; group
          exact htZ (ht_eq ▸ hconj)
        have hcomm : ∀ a ∈ Subgroup.zpowers (t : G), ∀ b ∈ Z, Commute a b := by
          intro a ha b hb
          have haS : a ∈ S := Subgroup.zpowers_le.mpr htS ha
          have hbS : b ∈ S := (show Z ≤ S from inf_le_left) hb
          have hbC : b ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hb).2
          exact Subgroup.mem_centralizer_iff.mp hbC a haS
        have hmemQ : (QuotientGroup.mk (Φ t) : Q) ∈ Subgroup.zpowers (QuotientGroup.mk t) := by
          obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.mem_sup_of_commute hcomm).mp hΦtB
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
          have hbS : b ∈ S := (show Z ≤ S from inf_le_left) hb
          have hbQ : (QuotientGroup.mk ⟨b, hbS⟩ : Q) = 1 := by
            rw [hZeq] at hb
            obtain ⟨c, hc, hcv⟩ := Subgroup.mem_map.mp hb
            have hsub : (⟨b, hbS⟩ : ↥S) = c := Subtype.ext hcv.symm
            rw [hsub]
            exact (QuotientGroup.eq_one_iff c).mpr hc
          refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
          have hsub : Φ t = (⟨a, Subgroup.zpowers_le.mpr htS ha⟩ : ↥S) * ⟨b, hbS⟩ := by
            apply Subtype.ext
            simpa using hab.symm
          calc (QuotientGroup.mk t : Q) ^ i
              = (QuotientGroup.mk (t ^ i) : Q) := (QuotientGroup.mk_zpow (N := Zc) t i).symm
            _ = (QuotientGroup.mk ⟨a, Subgroup.zpowers_le.mpr htS ha⟩ : Q) := by
                rw [show t ^ i = (⟨a, Subgroup.zpowers_le.mpr htS ha⟩ : ↥S) from Subtype.ext (by simpa using hi)]
            _ = (QuotientGroup.mk (Φ t) : Q) := by
                rw [hsub, QuotientGroup.mk_mul, hbQ, mul_one]
        have hne : (QuotientGroup.mk (Φ t) : Q) ≠ 1 := by
          intro hone
          exact hΦtZ (by
            rw [hZeq]
            exact Subgroup.mem_map_of_mem S.subtype ((QuotientGroup.eq_one_iff (Φ t)).mp hone))
        rcases eq_or_eq_inv_of_mem_zpowers_of_pow_three (hexpQ (QuotientGroup.mk t)) hmemQ hne with h | h
        · left; rw [hαmk]; exact h
        · right; rw [hαmk]; exact h
  rcases monoidHom_eq_id_or_inv_of_pow_three hexpQ α hα with hid | hinv
  · exfalso
    have hfix_all : ∀ t : ↥S, Φ t * t⁻¹ ∈ Zc := by
      intro t
      have hEq : (QuotientGroup.mk (Φ t) : Q) = QuotientGroup.mk t := by
        rw [← hαmk]; exact hid _
      rw [← (QuotientGroup.eq_one_iff (Φ t * t⁻¹))]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hEq, mul_inv_cancel]
    have hΦtZ : ∀ t : ↥S, (Φ t : G) * (t : G)⁻¹ ∈ Z := by
      intro t
      rw [hZeq]
      simpa using Subgroup.mem_map_of_mem S.subtype (hfix_all t)
    have hnotle : ¬ S ≤ Z := by
      intro hle
      have hcardS : Nat.card ↥S = 27 := hS.2.1
      have hcardZ : Nat.card ↥Z = 3 := card_inf_centralizer_eq_three hS
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨s, hsS, hsZ⟩ : ∃ s, s ∈ S ∧ s ∉ Z := by
      by_contra h
      apply hnotle
      intro x hx
      by_contra hxZ
      exact h ⟨x, hx, hxZ⟩
    let t : ↥S := ⟨s, hsS⟩
    have hΦsZ : (Φ t : G) * s⁻¹ ∈ Z := hΦtZ t
    have hγsS : γ * s * γ⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hγ s).mp hsS
    let w : G := s * (γ * s * γ⁻¹)
    have hwS : w ∈ S := S.mul_mem hsS hγsS
    have hγw_eq : γ * w * γ⁻¹ = (γ * s * γ⁻¹) * (Φ t : G) := by
      rw [hΦmem t]
      show γ * (s * (γ * s * γ⁻¹)) * γ⁻¹ = (γ * s * γ⁻¹) * (γ ^ 2 * s * (γ ^ 2)⁻¹)
      group
    have hγwS' : γ * w * γ⁻¹ ∈ S := by
      rw [hγw_eq]; exact S.mul_mem hγsS (Φ t).2
    have hγw_mk : (QuotientGroup.mk ⟨γ * w * γ⁻¹, hγwS'⟩ : Q) =
        QuotientGroup.mk ⟨w, hwS⟩ := by
      have hprod : (⟨γ * w * γ⁻¹, hγwS'⟩ : ↥S) = ⟨γ * s * γ⁻¹, hγsS⟩ * Φ t := by
        apply Subtype.ext
        simpa using hγw_eq
      rw [hprod, QuotientGroup.mk_mul]
      have hEq : (QuotientGroup.mk (Φ t) : Q) = QuotientGroup.mk t := by
        rw [← hαmk]; exact hid _
      calc (QuotientGroup.mk ⟨γ * s * γ⁻¹, hγsS⟩ : Q) * (QuotientGroup.mk (Φ t) : Q)
          = (QuotientGroup.mk ⟨γ * s * γ⁻¹, hγsS⟩ : Q) * (QuotientGroup.mk t : Q) := by rw [hEq]
        _ = (QuotientGroup.mk t : Q) * (QuotientGroup.mk ⟨γ * s * γ⁻¹, hγsS⟩ : Q) :=
              hcommQ.is_comm.comm _ _
        _ = (QuotientGroup.mk (t * ⟨γ * s * γ⁻¹, hγsS⟩) : Q) :=
              (QuotientGroup.mk_mul _ _ _).symm
        _ = (QuotientGroup.mk ⟨w, hwS⟩ : Q) := by
              congr 1
    have hγwZ : (γ * w * γ⁻¹) * w⁻¹ ∈ Z := by
      have hmem : ((⟨γ * w * γ⁻¹, hγwS'⟩ : ↥S) * (⟨w, hwS⟩ : ↥S)⁻¹) ∈ Zc := by
        apply (QuotientGroup.eq_one_iff ((⟨γ * w * γ⁻¹, hγwS'⟩ : ↥S) * (⟨w, hwS⟩ : ↥S)⁻¹)).mp
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hγw_mk, mul_inv_cancel]
      rw [hZeq]
      simpa using Subgroup.mem_map_of_mem S.subtype hmem
    by_cases hwZ : w ∈ Z
    · have hmem : γ * s * γ⁻¹ ∈ Subgroup.zpowers s ⊔ Z := by
        have heq : γ * s * γ⁻¹ = s⁻¹ * w := by
          show γ * s * γ⁻¹ = s⁻¹ * (s * (γ * s * γ⁻¹))
          group
        rw [heq]
        exact Subgroup.mul_mem_sup (Subgroup.inv_mem _ (Subgroup.mem_zpowers s)) hwZ
      exact h1 s hsS hsZ (mem_normalizer_sup_zpowers_of_mem_conj hγZ hmem)
    · have hmem : γ * w * γ⁻¹ ∈ Subgroup.zpowers w ⊔ Z := by
        have heq : γ * w * γ⁻¹ = ((γ * w * γ⁻¹) * w⁻¹) * w := by group
        rw [heq]
        have hmem' : ((γ * w * γ⁻¹) * w⁻¹) * w ∈ Z ⊔ Subgroup.zpowers w :=
          Subgroup.mul_mem_sup hγwZ (Subgroup.mem_zpowers w)
        rwa [sup_comm] at hmem'
      exact h1 w hwS hwZ (mem_normalizer_sup_zpowers_of_mem_conj hγZ hmem)
  · intro s hs
    change γ ^ 2 * s * (γ ^ 2)⁻¹ * s ∈ Z
    let t : ↥S := ⟨s, hs⟩
    have h := hinv (QuotientGroup.mk t)
    rw [hαmk] at h
    have hmem : Φ t * t ∈ Zc := by
      rw [← (QuotientGroup.eq_one_iff (Φ t * t))]
      rw [QuotientGroup.mk_mul, h, inv_mul_cancel]
    have hval : ((Φ t * t : ↥S) : G) = γ ^ 2 * s * (γ ^ 2)⁻¹ * s := by
      change (Φ t : G) * (t : G) = γ ^ 2 * s * (γ ^ 2)⁻¹ * s
      rw [hΦmem t]
    rw [hZeq]
    exact hval ▸ Subgroup.mem_map_of_mem S.subtype hmem


theorem inv_of_sq_normalizes {S : Subgroup G} (hS : Sec4.IsHeisThree S) {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (S : Set G))
    (h1 : ∀ s ∈ S, s ∉ S ⊓ Subgroup.centralizer (S : Set G) →
      γ ∉ Subgroup.normalizer
        ((Subgroup.zpowers s ⊔ (S ⊓ Subgroup.centralizer (S : Set G)) : Subgroup G) : Set G))
    (h2 : ∀ s ∈ S, s ∉ S ⊓ Subgroup.centralizer (S : Set G) →
      γ ^ 2 ∈ Subgroup.normalizer
        ((Subgroup.zpowers s ⊔ (S ⊓ Subgroup.centralizer (S : Set G)) : Subgroup G) : Set G)) :
    ∀ s ∈ S, γ ^ 2 * s * (γ ^ 2)⁻¹ * s ∈ S ⊓ Subgroup.centralizer (S : Set G) :=
  inv_of_sq_normalizes_aux hS hγ h1 h2

private theorem normalizer_iff_of_order_nine {S B B' : Subgroup G}
    (hS : Sec4.IsHeisThree S)
    (hcomm : ∀ x ∈ Subgroup.normalizer (S : Set G), ∀ y ∈ Subgroup.normalizer (S : Set G),
      x * y * x⁻¹ * y⁻¹ ∈ S)
    (htr : ∀ B ∈ {B : Subgroup G | B ≤ S ∧ Nat.card B = 9},
      ∀ B' ∈ {B : Subgroup G | B ≤ S ∧ Nat.card B = 9},
        ∃ x ∈ Subgroup.normalizer (S : Set G), B' = conjugate B x)
    (hB : B ≤ S) (hB' : B' ≤ S) (hcardB : Nat.card B = 9) (hcardB' : Nat.card B' = 9)
    {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer (B : Set G) ↔ g ∈ Subgroup.normalizer (B' : Set G) := by
  obtain ⟨y, hy, hyB⟩ := htr B ⟨hB, hcardB⟩ B' ⟨hB', hcardB'⟩
  have hSB : S ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_card_eq_nine hS hB hcardB
  have hcS : y * g * y⁻¹ * g⁻¹ ∈ S := hcomm y hy g hg
  have hcB : y * g * y⁻¹ * g⁻¹ ∈ Subgroup.normalizer (B : Set G) := hSB hcS
  have step1 : g ∈ Subgroup.normalizer (B : Set G) ↔
      y * g * y⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
    constructor
    · intro hgB
      have := Subgroup.mul_mem _ hcB hgB
      rwa [show (y * g * y⁻¹ * g⁻¹) * g = y * g * y⁻¹ from by group] at this
    · intro h
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hcB) h
      rwa [show (y * g * y⁻¹ * g⁻¹)⁻¹ * (y * g * y⁻¹) = g from by group] at this
  have hyBiff : ∀ x, x ∈ B' ↔ y * x * y⁻¹ ∈ B := by
    intro x
    rw [hyB, CFSG.mem_conjugate_iff]
  have step2 : y * g * y⁻¹ ∈ Subgroup.normalizer (B : Set G) ↔
      g ∈ Subgroup.normalizer (B' : Set G) := by
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h x
      rw [hyBiff x, hyBiff (g * x * g⁻¹)]
      have := h (y * x * y⁻¹)
      convert this using 1 <;> group
    · intro h a
      have := h (y⁻¹ * a * y)
      rw [hyBiff (y⁻¹ * a * y), hyBiff (g * (y⁻¹ * a * y) * g⁻¹)] at this
      convert this using 1 <;> group
  exact step1.trans step2

theorem exists_inv_of_transitive {S : Subgroup G}
    (hS : Sec4.IsHeisThree S)
    (hcomm : ∀ x ∈ Subgroup.normalizer (S : Set G), ∀ y ∈ Subgroup.normalizer (S : Set G),
      x * y * x⁻¹ * y⁻¹ ∈ S)
    (hexp : ∀ x ∈ Subgroup.normalizer (S : Set G), x ^ 8 ∈ S)
    (htr : ∀ B ∈ {B : Subgroup G | B ≤ S ∧ Nat.card B = 9},
      ∀ B' ∈ {B : Subgroup G | B ≤ S ∧ Nat.card B = 9},
        ∃ x ∈ Subgroup.normalizer (S : Set G), B' = conjugate B x) :
    ∃ n ∈ Subgroup.normalizer (S : Set G),
      ∀ s ∈ S, n * s * n⁻¹ * s ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
  classical
  let Z : Subgroup G := S ⊓ Subgroup.centralizer (S : Set G)
  let N := Subgroup.normalizer (S : Set G)
  have hScard : Nat.card ↥S = 27 := hS.2.1
  have hZcard : Nat.card ↥Z = 3 :=
    card_inf_centralizer_eq_three hS
  have hnotle : ¬ S ≤ Z := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨x0, hx0S, hx0Z⟩ : ∃ x, x ∈ S ∧ x ∉ Z := by
    by_contra h
    apply hnotle
    intro x hx
    by_contra hxZ
    exact h ⟨x, hx, hxZ⟩
  let B0 : Subgroup G := Subgroup.zpowers x0 ⊔ Z
  have hB0 := card_zpowers_sup_eq_nine hS hx0S hx0Z
  have hB0S : B0 ≤ S := hB0.1
  have hB0card : Nat.card ↥B0 = 9 := hB0.2
  have hnotleB0 : ¬ S ≤ B0 := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨y0, hy0S, hy0B0⟩ : ∃ x, x ∈ S ∧ x ∉ B0 := by
    by_contra h
    apply hnotleB0
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, hxB⟩
  have hy0Z : y0 ∉ Z := fun hz => hy0B0 (Subgroup.mem_sup_right hz)
  let B1 : Subgroup G := Subgroup.zpowers y0 ⊔ Z
  have hB1 := card_zpowers_sup_eq_nine hS hy0S hy0Z
  have hB1S : B1 ≤ S := hB1.1
  have hB1card : Nat.card ↥B1 = 9 := hB1.2
  obtain ⟨n, hnN, hnB⟩ := htr B0 ⟨hB0S, hB0card⟩ B1 ⟨hB1S, hB1card⟩
  have hSB0 : S ≤ Subgroup.normalizer (B0 : Set G) :=
    le_normalizer_of_card_eq_nine hS hB0S hB0card
  have hnNot : n ∉ Subgroup.normalizer (B0 : Set G) := by
    intro hn
    have hconj : conjugate B0 n = B0 := CFSG.conjugate_eq_self_of_mem_normalizer hn
    have hB1eq : B1 = B0 := by rw [hnB, hconj]
    exact hy0B0 (hB1eq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y0))
  have key : ∀ B : Subgroup G, B ≤ S → Nat.card ↥B = 9 → ∀ g ∈ N,
      (g ∈ Subgroup.normalizer (B : Set G) ↔ g ∈ Subgroup.normalizer (B0 : Set G)) := by
    intro B hBS hBcard g hg
    exact normalizer_iff_of_order_nine hS hcomm htr hBS hB0S hBcard hB0card hg
  obtain ⟨γ, hγN, hγNot, hγ2N⟩ : ∃ γ ∈ N, γ ∉ Subgroup.normalizer (B0 : Set G) ∧
      γ ^ 2 ∈ Subgroup.normalizer (B0 : Set G) := by
    by_cases h4 : n ^ 4 ∈ Subgroup.normalizer (B0 : Set G)
    · by_cases h2 : n ^ 2 ∈ Subgroup.normalizer (B0 : Set G)
      · exact ⟨n, hnN, hnNot, by simpa using h2⟩
      · refine ⟨n ^ 2, pow_mem hnN 2, h2, ?_⟩
        have h4' : (n ^ 2) ^ 2 = n ^ 4 := by rw [← pow_mul]
        rwa [h4']
    · refine ⟨n ^ 4, pow_mem hnN 4, h4, ?_⟩
      have h8 : n ^ 8 ∈ S := hexp n hnN
      have h8N : n ^ 8 ∈ Subgroup.normalizer (B0 : Set G) := hSB0 h8
      have h4' : (n ^ 4) ^ 2 = n ^ 8 := by rw [← pow_mul]
      rwa [h4']
  have h1 : ∀ s ∈ S, s ∉ Z → γ ∉ Subgroup.normalizer
      ((Subgroup.zpowers s ⊔ Z : Subgroup G) : Set G) := by
    intro s hsS hsZ
    have hBs := card_zpowers_sup_eq_nine hS hsS hsZ
    have hiff := key (Subgroup.zpowers s ⊔ Z) hBs.1 hBs.2 γ hγN
    exact fun hconj => hγNot (hiff.mp hconj)
  have h2 : ∀ s ∈ S, s ∉ Z → γ ^ 2 ∈ Subgroup.normalizer
      ((Subgroup.zpowers s ⊔ Z : Subgroup G) : Set G) := by
    intro s hsS hsZ
    have hBs := card_zpowers_sup_eq_nine hS hsS hsZ
    exact (key (Subgroup.zpowers s ⊔ Z) hBs.1 hBs.2 (γ ^ 2) (pow_mem hγN 2)).mpr hγ2N
  refine ⟨γ ^ 2, pow_mem hγN 2, ?_⟩
  exact inv_of_sq_normalizes hS hγN h1 h2


theorem comm_mem_and_pow_eight_mem {S : Subgroup G}
    (e : Subgroup.normalizer (S : Set G) ⧸ S.subgroupOf (Subgroup.normalizer (S : Set G)) ≃*
      Multiplicative (ZMod 8)) :
    (∀ x ∈ Subgroup.normalizer (S : Set G), ∀ y ∈ Subgroup.normalizer (S : Set G),
      x * y * x⁻¹ * y⁻¹ ∈ S) ∧ ∀ x ∈ Subgroup.normalizer (S : Set G), x ^ 8 ∈ S := by
  let N := Subgroup.normalizer (S : Set G)
  let Q := N ⧸ S.subgroupOf N
  have hcommQ : ∀ a b : Q, a * b = b * a := by
    intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have h8 : ∀ a : Multiplicative (ZMod 8), a ^ 8 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  constructor
  · intro x hx y hy
    have hQ : (QuotientGroup.mk ⟨x, hx⟩ : Q) * QuotientGroup.mk ⟨y, hy⟩ =
        QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨x, hx⟩ := hcommQ _ _
    have hmemN : (⟨x * y * x⁻¹ * y⁻¹, N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)⟩ : ↥N) ∈ S.subgroupOf N := by
      apply (QuotientGroup.eq_one_iff _).mp
      have hmk : (QuotientGroup.mk ⟨x * y * x⁻¹ * y⁻¹, N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)⟩ : Q) =
          (QuotientGroup.mk ⟨x, hx⟩ : Q) * (QuotientGroup.mk ⟨y, hy⟩ : Q) *
            (QuotientGroup.mk ⟨x, hx⟩ : Q)⁻¹ * (QuotientGroup.mk ⟨y, hy⟩ : Q)⁻¹ := by
        rw [show (⟨x * y * x⁻¹ * y⁻¹, N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)⟩ : ↥N) =
          ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ from rfl]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hmk, hQ]
      group
    exact Subgroup.mem_subgroupOf.mp hmemN
  · intro x hx
    have hmemN : (⟨x ^ 8, pow_mem hx 8⟩ : ↥N) ∈ S.subgroupOf N := by
      apply (QuotientGroup.eq_one_iff _).mp
      have hmk : (QuotientGroup.mk ⟨x ^ 8, pow_mem hx 8⟩ : Q) = (QuotientGroup.mk ⟨x, hx⟩ : Q) ^ 8 :=
        QuotientGroup.mk_pow (N := S.subgroupOf N) ⟨x, hx⟩ 8
      have hone : (QuotientGroup.mk ⟨x ^ 8, pow_mem hx 8⟩ : Q) = 1 := by
        apply e.injective
        rw [map_one, hmk, map_pow]
        exact h8 _
      exact hone
    exact Subgroup.mem_subgroupOf.mp hmemN

omit [Finite G] in
theorem kg1_holds :
    KG1 := by
  intro d S hcard hd1 hdS hSC
  have hJ2card : Nat.card J2 = 604800 :=
    (Nat.card_congr CFSG.ComponentClassification.J2Cover.nativeEquivP.toEquiv).trans
      Sec4.Sporadic.J2.card_GJ
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hSylowCard : Nat.card ↥S = 3 ^ (Nat.card J2).factorization 3 := by
    rw [hcard, hJ2card]
    rw [CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  let P : Sylow 3 J2 := Sylow.ofCard S hSylowCard
  have hPS : (P : Subgroup J2) = S := Sylow.coe_ofCard S hSylowCard
  have h123 : Sec4.Sporadic.J2.Pt123 S := by
    have h := Sec4.Sporadic.J2.forall_sylow_of_P3
      (fun _ _ P => Sec4.Sporadic.J2.Pt123 P)
      (fun _ _ _ _ φ _ hP => hP.map φ)
      Sec4.Sporadic.J2.pt123_P3 J2 ⟨MulEquiv.refl _⟩ P
    rwa [hPS] at h
  have hS : Sec4.IsHeisThree S := h123.1.1
  obtain ⟨e⟩ := h123.1.2
  have hcomm := (comm_mem_and_pow_eight_mem e).1
  have hexp := (comm_mem_and_pow_eight_mem e).2
  have htr := h123.2.1
  let Z : Subgroup J2 := S ⊓ Subgroup.centralizer (S : Set J2)
  have hZcard : Nat.card ↥Z = 3 := card_inf_centralizer_eq_three hS
  have hd3 : d ^ 3 = 1 := by
    have h : (⟨d, hdS⟩ : ↥S) ^ 3 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨d, hdS⟩ : ↥S)
      rwa [hS.2.2] at this
    simpa using congrArg Subtype.val h
  have hordd : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hzpowd_card : Nat.card ↥(Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, hordd]
  have hdC : d ∈ Subgroup.centralizer (S : Set J2) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
  have hzpowd_le : Subgroup.zpowers d ≤ Z :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdS, hdC⟩)
  have hZeq : Z = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge hzpowd_le (by rw [hZcard, hzpowd_card])).symm
  have hcard9 : ∀ T : Subgroup J2, Subgroup.zpowers d < T → T < S → Nat.card ↥T = 9 := by
    intro T hdT hTS
    have hdvd : Nat.card ↥T ∣ 3 ^ 3 := by
      have := Subgroup.card_dvd_of_le hTS.le
      rwa [hcard, show (27 : ℕ) = 3 ^ 3 by norm_num] at this
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hge : 3 < 3 ^ k := by
      rw [← hkeq, ← hzpowd_card]
      exact Subgroup.card_lt_of_lt hdT
    have hlt : 3 ^ k < 27 := by
      rw [← hkeq, ← hcard]
      exact Subgroup.card_lt_of_lt hTS
    have hk0 : k ≠ 0 := by rintro rfl; norm_num at hge
    have hk1 : k ≠ 1 := by rintro rfl; norm_num at hge
    have hk3 : k ≠ 3 := by rintro rfl; norm_num at hlt
    rw [hkeq, show k = 2 by omega]
    norm_num
  refine ⟨?_, ?_⟩
  · intro T₁ T₂ h1T₁ hT₁S h1T₂ hT₂S
    obtain ⟨x, hxN, hxT⟩ := htr T₁ ⟨hT₁S.le, hcard9 T₁ h1T₁ hT₁S⟩ T₂
      ⟨hT₂S.le, hcard9 T₂ h1T₂ hT₂S⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨Subgroup.inv_mem _ hxN, ?_⟩
      have hxZ : x ∈ Subgroup.normalizer (Z : Set J2) :=
        CFSG.RankThree.LocalRank.normalizer_le_normalizer_inf_centralizer S hxN
      rw [← hZeq]
      exact Subgroup.inv_mem _ hxZ
    · exact hxT.symm
  · obtain ⟨n, hnN, hnconj⟩ := exists_inv_of_transitive hS hcomm hexp htr
    refine ⟨n, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨hnN, ?_⟩
      have hnZ : n ∈ Subgroup.normalizer (Z : Set J2) :=
        CFSG.RankThree.LocalRank.normalizer_le_normalizer_inf_centralizer S hnN
      rw [← hZeq]
      exact hnZ
    · intro s hs
      rw [← hZeq]
      exact hnconj s hs

end CFSG.RankThree.PartTwo.J2Residue
