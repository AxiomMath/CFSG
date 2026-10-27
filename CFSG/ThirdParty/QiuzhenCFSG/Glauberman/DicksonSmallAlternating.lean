module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

namespace CFSG
end CFSG
open CFSG

/-!
# Small alternating and symmetric recognition lemmas

These low-order action arguments form an independent Dickson-classification
compilation boundary.
-/

namespace CFSG.Glauberman
namespace Dickson

universe u

/-- Huppert II.8.17(b): a group of order twelve with four Sylow `3`-subgroups is `A₄`. -/
public theorem huppert_II_8_17_b_order_twelve_four_sylow_three
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 12) (hSylow : Nat.card (Sylow 3 G) = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  let Ω := Sylow 3 G
  let := Fintype.ofFinite Ω
  have hΩcard : Fintype.card Ω = 4 := by
    simpa [Ω, Nat.card_eq_fintype_card] using hSylow
  have hfac12 : (Nat.factorization 12) 3 = 1 := by
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
  have hnormalizer_eq :
      ∀ P : Ω, Subgroup.normalizer (P : Set G) =
        (P : Subgroup G) := by
    intro P
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hindex :
        (Subgroup.normalizer (P : Set G)).index = 4 := by
      rw [← P.card_eq_index_normalizer, hSylow]
    have hNcard :
        Nat.card (Subgroup.normalizer (P : Set G)) = 3 := by
      have hmul :=
        (Subgroup.normalizer (P : Set G)).card_mul_index
      rw [hindex, hGcard] at hmul
      omega
    exact
      (Subgroup.eq_of_le_of_card_ge
        (show (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) from
          Subgroup.le_normalizer) (by omega)).symm
  let act := MulAction.toPermHom G Ω
  have hker_le : ∀ P : Ω, act.ker ≤ (P : Subgroup G) := by
    intro P x hx
    have hxperm : act x = 1 := hx
    have hxfix : x • P = P := by
      have h := DFunLike.congr_fun hxperm P
      simpa [act] using h
    have hxstab : x ∈ MulAction.stabilizer G P := hxfix
    rw [Sylow.stabilizer_eq_normalizer, hnormalizer_eq P] at hxstab
    exact hxstab
  have hact_inj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    let P : Ω := default
    obtain ⟨Q, hQP⟩ :=
      Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) P
    have hxP : x ∈ (P : Subgroup G) := hker_le P hx
    have hxQ : x ∈ (Q : Subgroup G) := hker_le Q hx
    by_contra hxone
    let I : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G)
    have hxI : x ∈ I := ⟨hxP, hxQ⟩
    have hIcard_ne_one : Nat.card I ≠ 1 := by
      intro hIcard
      have hIbot : I = ⊥ := Subgroup.card_eq_one.mp hIcard
      rw [hIbot, Subgroup.mem_bot] at hxI
      exact hxone hxI
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hQcard : Nat.card Q = 3 := by
      rw [Q.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hIdivP : Nat.card I ∣ Nat.card P := by
      rw [← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show I ≤ (P : Subgroup G) from inf_le_left)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card (I.subgroupOf (P : Subgroup G))
    have hIcard : Nat.card I = 3 := by
      have hdiv3 : Nat.card I ∣ 3 := by simpa [hPcard] using hIdivP
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
      · exact (hIcard_ne_one h).elim
      · exact h
    have hIP : I = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hIQ : I = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    apply hQP
    exact Sylow.ext (hIQ.symm.trans hIP)
  let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
  let actFin : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eΩ).toMonoidHom.comp act
  have hactFin_inj : Function.Injective actFin := by
    intro x y hxy
    apply hact_inj
    apply (Equiv.permCongrHom eΩ).injective
    simpa [actFin] using hxy
  let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
  have hrange_inj : Function.Injective actFin.rangeRestrict := by
    intro x y hxy
    exact hactFin_inj (congrArg Subtype.val hxy)
  let eRange : G ≃* K :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨hrange_inj, MonoidHom.rangeRestrict_surjective actFin⟩
  have hKcard : Nat.card K = 12 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hpermcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hKindex : K.index = 2 := by
    have hmul := K.index_mul_card
    rw [hKcard, hpermcard] at hmul
    omega
  have hKalt : K = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hKindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hKalt)⟩

/-- Huppert II.8.17(c): a group of order twenty-four with four Sylow
`3`-subgroups and trivial center is `S₄`. -/
public theorem huppert_II_8_17_c_order_twenty_four_four_sylow_three
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 24) (hSylow : Nat.card (Sylow 3 G) = 4)
    (hcenter : Subgroup.center G = ⊥) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  let Ω := Sylow 3 G
  let := Fintype.ofFinite Ω
  have hΩcard : Fintype.card Ω = 4 := by
    simpa [Ω, Nat.card_eq_fintype_card] using hSylow
  let act := MulAction.toPermHom G Ω
  have hnormalizer_card (P : Ω) :
      Nat.card (Subgroup.normalizer (P : Set G)) = 6 := by
    have hindex :
        (Subgroup.normalizer (P : Set G)).index = 4 := by
      rw [← P.card_eq_index_normalizer, hSylow]
    have hmul :=
      (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hindex, hGcard] at hmul
    omega
  have hker_le_normalizer (P : Ω) :
      act.ker ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    have hxperm : act x = 1 := hx
    have hxfix : x • P = P := by
      have h := DFunLike.congr_fun hxperm P
      simpa [act] using h
    exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
  have hthree_not_dvd_ker : ¬ 3 ∣ Nat.card act.ker := by
    intro hthree
    obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' 3 hthree
    have hxGorder : orderOf (x : G) = 3 :=
      (Subgroup.orderOf_coe x).trans hxorder
    have hXp : IsPGroup 3 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, hxGorder, pow_one])
    obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
    obtain ⟨Q, hQP⟩ :=
      Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) P
    have hfac24 : (Nat.factorization 24) 3 = 1 := by
      have hle : 1 ≤ (Nat.factorization 24) 3 :=
        ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization
          (by norm_num)).mp (by norm_num)
      have hnle : ¬ 2 ≤ (Nat.factorization 24) 3 := by
        intro h
        have hdvd :=
          ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization
            (by norm_num)).mpr h
        norm_num at hdvd
      omega
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard, hfac24]
      norm_num
    have hPker : (P : Subgroup G) ≤ act.ker := by
      have hXcard : Nat.card (Subgroup.zpowers (x : G)) = 3 := by
        rw [Nat.card_zpowers, hxGorder]
      have hXP_eq :
          Subgroup.zpowers (x : G) = (P : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hXP (by rw [hXcard, hPcard])
      rw [← hXP_eq]
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact act.ker.zpow_mem x.2 n
    have hPnormalizesQ :
        (P : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) :=
      fun y hy => hker_le_normalizer Q (hPker hy)
    have hsupP :
        IsPGroup 3 ((P : Subgroup G) ⊔ (Q : Subgroup G) : Subgroup G) :=
      P.isPGroup'.to_sup_of_normal_right' Q.isPGroup' hPnormalizesQ
    have hsup_eq :
        (P : Subgroup G) ⊔ (Q : Subgroup G) = (Q : Subgroup G) :=
      Q.is_maximal' hsupP le_sup_right
    have hPleQ : (P : Subgroup G) ≤ Q := by
      rw [← hsup_eq]
      exact le_sup_left
    have hP_eq_Q : (P : Subgroup G) = Q :=
      Subgroup.eq_of_le_of_card_ge hPleQ (by
        rw [Nat.card_congr (Sylow.equiv P Q).toEquiv])
    exact hQP (Sylow.ext hP_eq_Q.symm)
  have hker_card_dvd_six : Nat.card act.ker ∣ 6 := by
    let P : Ω := default
    simpa [hnormalizer_card P] using
      Subgroup.card_dvd_of_le (hker_le_normalizer P)
  have hker_card_cases : Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
    have hpos : 0 < Nat.card act.ker := Nat.card_pos
    have hle : Nat.card act.ker ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hker_card_dvd_six
    interval_cases Nat.card act.ker <;> norm_num at *
  have hker_bot : act.ker = ⊥ := by
    rcases hker_card_cases with hone | htwo
    · exact Subgroup.card_eq_one.mp hone
    · exfalso
      obtain ⟨z, hz_ne, hz_unique⟩ :=
        (Nat.card_eq_two_iff' (1 : act.ker)).mp htwo
      have hz_center : (z : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        let zg : act.ker :=
          ⟨g * (z : G) * g⁻¹,
            (inferInstance : act.ker.Normal).conj_mem (z : G) z.2 g⟩
        have hzg_ne : zg ≠ 1 := by
          intro hzg
          have hval := congrArg Subtype.val hzg
          change g * (z : G) * g⁻¹ = 1 at hval
          apply hz_ne
          apply Subtype.ext
          calc
            (z : G) = g⁻¹ * (g * (z : G) * g⁻¹) * g := by group
            _ = 1 := by rw [hval]; simp
        have hzg_eq : zg = z := hz_unique zg hzg_ne
        have hval := congrArg Subtype.val hzg_eq
        change g * (z : G) * g⁻¹ = (z : G) at hval
        calc
          g * (z : G) = (g * (z : G) * g⁻¹) * g := by group
          _ = (z : G) * g := by rw [hval]
      have hz_bot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← hcenter]
        exact hz_center
      apply hz_ne
      apply Subtype.ext
      simpa using hz_bot
  have hact_inj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hker_bot
  let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
  let actFin : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eΩ).toMonoidHom.comp act
  have hactFin_inj : Function.Injective actFin := by
    intro x y hxy
    apply hact_inj
    apply (Equiv.permCongrHom eΩ).injective
    simpa [actFin] using hxy
  let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
  let eRange : G ≃* K :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨fun x y hxy => hactFin_inj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin⟩
  have hKcard : Nat.card K = 24 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hpermcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hKtop : K = ⊤ :=
    Subgroup.eq_top_of_card_eq (H := K) (hKcard.trans hpermcard.symm)
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hKtop) |>.trans
    (Subgroup.topEquiv :
      (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≃* Equiv.Perm (Fin 4))⟩

end Dickson
end CFSG.Glauberman
