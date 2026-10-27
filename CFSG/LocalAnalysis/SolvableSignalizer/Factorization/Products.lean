module

public import CFSG.LocalAnalysis.SolvableSignalizer.Factorization.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
import CFSG.LocalAnalysis.SolvableSignalizer.HallProduct
import CFSG.LocalAnalysis.SolvableSignalizer.PrimeSubfunctor
import CFSG.LocalAnalysis.SolvableSignalizer.Quotient
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerAuxiliaryProduct

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise

section

variable {A G : Type*} [CommGroup A] [Group G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G} {M Q₀ : Subgroup G}

private lemma isInvariant_subgroupOf_restrict {K H : Subgroup G}
    (hK : IsInvariant α K) (hH : IsInvariant α H) :
    IsInvariant (restrictAction α K hK) (H.subgroupOf K) := by
  intro b
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change α b (y : G) ∈ H
    exact hH b ▸ Subgroup.mem_map.mpr ⟨(y : G), hy, rfl⟩
  · intro hx
    refine Subgroup.mem_map.mpr ⟨(restrictAction α K hK b)⁻¹ x, ?_, by simp⟩
    change (((restrictAction α K hK b)⁻¹ x : K) : G) ∈ H
    rw [(map_inv (restrictAction α K hK) b).symm, restrictAction_apply]
    exact hH b⁻¹ ▸ Subgroup.mem_map.mpr ⟨(x : G), hx, rfl⟩

private lemma mem_subgroupOf_inf_fixedSubgroup {K H : Subgroup G}
    (hK : IsInvariant α K) (b : A) (k : K) :
    k ∈ (H.subgroupOf K) ⊓ fixedSubgroup (restrictAction α K hK) b ↔
      (k : G) ∈ fixedIn α H b := by
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_fixedSubgroup, mem_fixedIn]
  constructor
  · rintro ⟨hH, hfix⟩
    exact ⟨hH, by simpa [restrictAction_apply] using congrArg Subtype.val hfix⟩
  · rintro ⟨hH, hfix⟩
    exact ⟨hH, Subtype.ext (by simpa [restrictAction_apply] using hfix)⟩

private theorem le_normalizer_iSup_conjugate (H Q K : Subgroup G)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    H ≤ Subgroup.normalizer (↑(⨆ k : K, conjugate Q (k : G)) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro c hc d hd
  have hQc : conjugate Q c = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (hHQ hc))
  have hmap : (⨆ k : K, conjugate Q (k : G)).map (MulAut.conj c).toMonoidHom ≤
      ⨆ k : K, conjugate Q (k : G) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    have hkK : c * (k : G) * c⁻¹ ∈ K := Subgroup.le_normalizer_iff.mp hHK c hc (k : G) k.2
    have hstep : conjugate Q (c * (k : G) * c⁻¹) = conjugate Q ((k : G) * c⁻¹) := by
      rw [mul_assoc, ← conjugate_conjugate Q c, hQc]
    rw [map_conj_conjugate, ← hstep]
    exact le_iSup_of_le ⟨c * (k : G) * c⁻¹, hkK⟩ le_rfl
  simpa [MulAut.conj_apply] using hmap (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hd)

private theorem factorizationL_le_normalizer :
    factorizationL θ Q₀ ≤ Subgroup.normalizer (factorizationQ Q₀ : Set G) :=
  completionIn_le θ _

end

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p q : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G} {M Q₀ : Subgroup G}

private theorem nontrivial_of_factorizationDatum (f : FactorizationDatum p α θ q M Q₀) :
    Nontrivial A :=
  Finite.one_lt_card_iff_nontrivial.mp <| calc
    1 < 2 ^ 3 := by norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left f.solvable.prime.two_le 3
    _ ≤ Nat.card A := f.rank_three

private theorem coe_factorizationK_eq_mul (f : FactorizationDatum p α θ q M Q₀)
    (B : Subgroup A) (hB : B ∈ factorizationHyperplanes p) :
    (factorizationK α θ q : Set G) = (factorizationHyperplaneCore θ q B : Set G) *
        ((factorizationK α θ q ⊓ factorizationL θ Q₀ : Subgroup G) : Set G) ∧
      (factorizationK α θ q : Set G) =
        ((factorizationK α θ q ⊓ factorizationL θ Q₀ : Subgroup G) : Set G) *
        (factorizationHyperplaneCore θ q B : Set G) := by
  classical
  have hd := f.solvable
  set K := factorizationK α θ q
  set L := factorizationL θ Q₀
  set KB := factorizationHyperplaneCore θ q B
  obtain ⟨hKB_le, hKB_inv, hCommon_norm, _⟩ := FactorizationDatum.hyperplaneCore_spec f B hB
  obtain ⟨_, _, _, hL_compat, ⟨hK_compat, -⟩, _, _⟩ := FactorizationDatum.basic_subgroups f
  have hK_inv : IsInvariant α K := hK_compat.1
  have hBcard : p ^ 2 ≤ Nat.card B := by
    have hmul : Nat.card B * p = Nat.card A := by
      rw [← hB]; exact Subgroup.card_mul_index B
    have h3 : p ^ 3 ≤ Nat.card B * p := by rw [hmul]; exact f.rank_three
    rw [pow_succ] at h3
    exact Nat.le_of_mul_le_mul_right h3 hd.prime.pos
  have : CFSG.IsElementaryAbelian p B :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (by simpa using hd.exponent (x : A))) }
  have htheta : ∀ b : A, b ≠ 1 → b ∈ B →
      (θ b : Set G) = ((θ b ⊓ KB : Subgroup G) : Set G) * ((θ b ⊓ L : Subgroup G) : Set G) := by
    intro b hb hbB
    have hO_le : factorizationComplementCore q (θ b) ≤ θ b ⊓ KB :=
      le_inf (Subgroup.map_subtype_le _)
        (le_iSup_of_le b (le_iSup_of_le hbB (le_iSup_of_le hb le_rfl)))
    apply Set.Subset.antisymm
    · rw [FactorizationDatum.coe_value_eq_mul f b hb]
      exact Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr hO_le)
    · rintro x ⟨y, hy, z, hz, rfl⟩
      exact (θ b).mul_mem hy.1 hz.1
  have hCK : ∀ b : A, b ≠ 1 → b ∈ B →
      (fixedIn α K b : Set G) = (fixedIn α KB b : Set G) * (fixedIn α (K ⊓ L) b : Set G) := by
    intro b hb hbB
    apply Set.Subset.antisymm
    · intro x hx
      have hxθ : x ∈ (θ b : Set G) := hK_compat.2.2.2 b hb hx
      rw [htheta b hb hbB] at hxθ
      rcases hxθ with ⟨y, hy, z, hz, hyz⟩
      have hzK : z ∈ K := by
        have hmem : y⁻¹ * x ∈ K := K.mul_mem (K.inv_mem (hKB_le hy.2)) hx.1
        rwa [← hyz, inv_mul_cancel_left] at hmem
      exact ⟨y, ⟨hy.2, hd.central b hb hy.1⟩, z, ⟨⟨hzK, hz.2⟩, hd.central b hb hz.1⟩, hyz⟩
    · rintro x ⟨y, hy, z, hz, rfl⟩
      exact ⟨K.mul_mem (hKB_le hy.1) hz.1.1, (fixedSubgroup α b).mul_mem hy.2 hz.2⟩
  have hCK_le_common : fixedInBySubgroup α K B ≤ commonSignalizer θ B := by
    intro x hx
    simp only [commonSignalizer, Subgroup.mem_iInf]
    exact fun b hbB hb =>
      hK_compat.2.2.2 b hb ⟨hx.1, (mem_fixedBySubgroup α B x).mp hx.2 b hbB⟩
  let α' : B →* MulAut K := (restrictAction α K hK_inv).comp B.subtype
  have hX : IsInvariant α' (KB.subgroupOf K) :=
    fun b => isInvariant_subgroupOf_restrict hK_inv hKB_inv (b : A)
  have hY : IsInvariant α' ((K ⊓ L).subgroupOf K) :=
    fun b => isInvariant_subgroupOf_restrict hK_inv (hK_inv.inf hL_compat.1) (b : A)
  have hnorm :
      actionFixedAll α' ≤ Subgroup.normalizer ((KB.subgroupOf K : Subgroup K) : Set K) := by
    intro c hc
    have hcG : (c : G) ∈ fixedInBySubgroup α K B := by
      refine ⟨c.property, (mem_fixedBySubgroup α B (c : G)).mpr fun b hbB => ?_⟩
      have hcb := (mem_fixedBySubgroup α' ⊤ c).mp hc ⟨b, hbB⟩ (Subgroup.mem_top _)
      simpa [α', restrictAction_apply] using congrArg Subtype.val hcb
    have hnormG : (c : G) ∈ Subgroup.normalizer (KB : Set G) := hCommon_norm (hCK_le_common hcG)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change (x : G) ∈ KB ↔ ((c * x * c⁻¹ : K) : G) ∈ KB
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (Subgroup.mem_normalizer_iff.mp hnormG) (x : G)
  have hlocal : ∀ b : B, b ≠ 1 →
      (fixedSubgroup α' b : Set K) =
        (KB.subgroupOf K ⊓ fixedSubgroup α' b : Subgroup K) *
          ((K ⊓ L).subgroupOf K ⊓ fixedSubgroup α' b : Subgroup K) := by
    intro b hb
    have hkey := hCK (b : A) (fun h => hb (Subtype.ext h)) b.property
    apply Set.Subset.antisymm
    · intro k hk
      have hkG : (k : G) ∈ (fixedIn α K (b : A) : Set G) := ⟨k.property, by
        simpa [α', restrictAction_apply] using
          congrArg Subtype.val ((mem_fixedSubgroup α' b k).mp hk)⟩
      rw [hkey] at hkG
      rcases hkG with ⟨y, hy, z, hz, hyz⟩
      exact ⟨⟨y, hKB_le hy.1⟩,
        (mem_subgroupOf_inf_fixedSubgroup hK_inv (b : A) ⟨y, hKB_le hy.1⟩).mpr hy,
        ⟨z, hz.1.1⟩, (mem_subgroupOf_inf_fixedSubgroup hK_inv (b : A) ⟨z, hz.1.1⟩).mpr hz,
        Subtype.ext hyz⟩
    · rintro k ⟨x, hx, y, hy, rfl⟩
      have hxG := (mem_subgroupOf_inf_fixedSubgroup hK_inv (b : A) x).mp hx
      have hyG := (mem_subgroupOf_inf_fixedSubgroup hK_inv (b : A) y).mp hy
      exact (mem_fixedSubgroup α' b (x * y)).mpr (Subtype.ext (by
        simp only [α', MonoidHom.comp_apply, restrictAction_apply, Subgroup.coe_mul, map_mul]
        exact congrArg₂ (· * ·) (by simpa using hxG.2) (by simpa using hyG.2)))
  have hsplit := mul_eq_univ_of_fixedSubgroup_eq_mul (A := B) (G := K) p hd.prime α' hBcard
    (hd.prime.coprime_iff_not_dvd.mp hK_compat.2.2.1) (KB.subgroupOf K) ((K ⊓ L).subgroupOf K)
    hX hY hnorm hlocal
  have hset : (K : Set G) = (KB : Set G) * ((K ⊓ L : Subgroup G) : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hmem : (⟨x, hx⟩ : K) ∈ (KB.subgroupOf K : Set K) * ((K ⊓ L).subgroupOf K : Set K) := by
        rw [hsplit]; exact Set.mem_univ _
      rcases Set.mem_mul.mp hmem with ⟨a, ha, c, hc, hac⟩
      exact ⟨(a : G), ha, (c : G), hc, by simpa using congrArg Subtype.val hac⟩
    · rintro x ⟨a, ha, c, hc, rfl⟩
      exact K.mul_mem (hKB_le ha) hc.1
  refine ⟨hset, Set.Subset.antisymm (fun x hx => ?_) ?_⟩
  · have hx' : x⁻¹ ∈ (K : Set G) := K.inv_mem hx
    rw [hset] at hx'
    rcases hx' with ⟨a, ha, c, hc, hac⟩
    refine ⟨c⁻¹, (K ⊓ L).inv_mem hc, a⁻¹, KB.inv_mem ha, ?_⟩
    rw [← inv_inv x, ← hac, mul_inv_rev]
  · rintro x ⟨a, ha, c, hc, rfl⟩
    exact K.mul_mem ha.1 (hKB_le hc)

private theorem factorizationD_eq_iSup_conjugate
    (f : FactorizationDatum p α θ q M Q₀)
    (B : Subgroup A) (hB : B ∈ factorizationHyperplanes p) :
    factorizationD α θ q Q₀ =
        (⨆ k : factorizationK α θ q, conjugate (factorizationQ Q₀) (k : G)) ∧
      factorizationD α θ q Q₀ =
        (⨆ k : factorizationHyperplaneCore θ q B,
          conjugate (factorizationQ Q₀) (k : G)) ∧
      factorizationQ Q₀ ≠ ⊥ ∧ factorizationQ Q₀ ≤ factorizationD α θ q Q₀ ∧
      factorizationD α θ q Q₀ ≤ factorizationG₀ α θ q Q₀ ∧
      ((factorizationD α θ q Q₀).subgroupOf (factorizationG₀ α θ q Q₀)).Normal := by
  have hQne : factorizationQ Q₀ ≠ ⊥ := (FactorizationDatum.basic_subgroups f).1
  have hKBle := (FactorizationDatum.hyperplaneCore_spec f B hB).1
  have hsplit := (coe_factorizationK_eq_mul f B hB).2
  set Q := factorizationQ Q₀
  set K := factorizationK α θ q
  set L := factorizationL θ Q₀
  set KB := factorizationHyperplaneCore θ q B
  set G₀ := factorizationG₀ α θ q Q₀
  set E : Subgroup G := ⨆ k : K, conjugate Q (k : G) with hE
  have hstep : ∀ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ E := by
    intro k hk
    rw [hE, Subgroup.map_iSup]
    refine iSup_le fun k' => ?_
    rw [map_conj_conjugate]
    exact le_iSup (fun k'' : K => conjugate Q (k'' : G))
      ⟨(k' : G) * k⁻¹, K.mul_mem k'.2 (inv_mem hk)⟩
  have hK_norm : K ≤ Subgroup.normalizer (E : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hstep k hk) ?_
    have hcomp : (MulAut.conj k).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h3 := Subgroup.map_mono (f := (MulAut.conj k).toMonoidHom) (hstep k⁻¹ (inv_mem hk))
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h3
  have hQ_le_E : Q ≤ E := le_iSup_of_le (⟨1, K.one_mem⟩ : K) (by simp)
  have hK_le_G₀ : K ≤ G₀ := le_sup_left
  have hG₀_norm : G₀ ≤ Subgroup.normalizer (E : Set G) :=
    sup_le hK_norm (hQ_le_E.trans (Subgroup.le_normalizer (H := E)))
  have hD_eq_E : factorizationD α θ q Q₀ = E := by
    apply le_antisymm
    · refine iSup_le fun g => ?_
      have hfix : E.map (MulAut.conj (g : G)⁻¹).toMonoidHom = E :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ (hG₀_norm g.2))
      exact (Subgroup.map_mono hQ_le_E).trans hfix.le
    · exact iSup_le fun k =>
        le_iSup (fun g : G₀ => conjugate Q (g : G)) ⟨(k : G), hK_le_G₀ k.2⟩
  have hD_le_G₀ : factorizationD α θ q Q₀ ≤ G₀ := by
    rw [hD_eq_E, hE]
    refine iSup_le fun k => ?_
    have hkG₀ : (k : G) ∈ G₀ := hK_le_G₀ k.2
    rintro x ⟨y, hy, rfl⟩
    change MulAut.conj (k : G)⁻¹ y ∈ G₀
    rw [MulAut.conj_apply]
    exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hkG₀) (Subgroup.mem_sup_right hy : y ∈ G₀))
      (by simpa using hkG₀)
  have hD_eq_EB : factorizationD α θ q Q₀ = ⨆ b : KB, conjugate Q (b : G) := by
    rw [hD_eq_E]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      have hk : (k : G) ∈ ((K ⊓ L : Subgroup G) : Set G) * (KB : Set G) := hsplit ▸ k.2
      rcases Set.mem_mul.mp hk with ⟨n, hn, b, hb, hnb⟩
      have hQn : conjugate Q n = Q :=
        conjugate_eq_self_of_mem_normalizer (factorizationL_le_normalizer hn.2)
      rw [← hnb, ← conjugate_conjugate, hQn]
      exact le_iSup (fun b' : KB => conjugate Q (b' : G)) ⟨b, hb⟩
    · exact iSup_le fun b =>
        le_iSup (fun k : K => conjugate Q (k : G)) ⟨(b : G), hKBle b.2⟩
  refine ⟨hD_eq_E.trans hE, hD_eq_EB, hQne, hD_eq_E ▸ hQ_le_E, hD_le_G₀, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD_le_G₀, hD_eq_E]
  exact hG₀_norm

theorem FactorizationDatum.coe_factorizationG₀_eq_mul (f : FactorizationDatum p α θ q M Q₀) :
    (factorizationG₀ α θ q Q₀ : Set G) =
        (factorizationK α θ q : Set G) * (factorizationQ Q₀ : Set G) ∧
      (factorizationG₀ α θ q Q₀ : Set G) =
        (factorizationQ Q₀ : Set G) * (factorizationK α θ q : Set G) ∧
      IsInvariant α (factorizationG₀ α θ q Q₀) ∧
      ¬ p ∣ Nat.card (factorizationG₀ α θ q Q₀) := by
  classical
  have hd := f.solvable
  obtain ⟨_, _, ⟨⟨hQinv, -, hQcop, -⟩, -⟩, _, ⟨⟨hKinv, -, hKcop, -⟩, -⟩, _, _⟩ :=
    FactorizationDatum.basic_subgroups f
  have := hd.isElementaryAbelian
  have := nontrivial_of_factorizationDatum f
  have hgeneration : (⨆ (B : Subgroup A) (_ : B.index = p),
      fixedInBySubgroup α (factorizationQ Q₀) B) = factorizationQ Q₀ := by
    have hm := congrArg (Subgroup.map (factorizationQ Q₀).subtype)
      (iSup_fixedBySubgroup_index_eq_top p hd.prime (restrictAction α (factorizationQ Q₀) hQinv)
        (hd.prime.coprime_iff_not_dvd.mp hQcop))
    simpa only [Subgroup.map_iSup, fixedBySubgroup_restrictAction_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype] using hm
  have hpreserved : factorizationQ Q₀ ≤
      SignalizerFunctor.Helpers.setLeftStabilizer
        (SignalizerFunctor.Helpers.subgroupProduct (factorizationK α θ q) (factorizationQ Q₀)) := by
    conv_lhs => rw [← hgeneration]
    refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨hcore, _, _, hnorm⟩ := FactorizationDatum.hyperplaneCore_spec f B hB
    exact SignalizerFunctor.Helpers.subgroup_product_left_stabilized
      (factorizationK α θ q) (factorizationQ Q₀) (fixedInBySubgroup α (factorizationQ Q₀) B)
      (factorizationHyperplaneCore θ q B) (factorizationK α θ q ⊓ factorizationL θ Q₀)
      inf_le_left hcore inf_le_left hnorm (inf_le_right.trans factorizationL_le_normalizer)
      (coe_factorizationK_eq_mul f B hB).1.symm
  obtain ⟨hprod, hreverse⟩ := SignalizerFunctor.Helpers.permuting_subgroup_product_eq_sup
    (factorizationK α θ q) (factorizationQ Q₀) hpreserved
  have hcop := SignalizerFunctor.Helpers.coprime_sup_of_permuting_product
    p hd.prime (factorizationK α θ q) (factorizationQ Q₀) hKcop hQcop hprod
  refine ⟨hprod.symm, hprod.symm.trans hreverse.symm, fun a => ?_,
    hd.prime.coprime_iff_not_dvd.mp hcop⟩
  change (factorizationK α θ q ⊔ factorizationQ Q₀).map (α a).toMonoidHom = _
  rw [Subgroup.map_sup, hKinv a, hQinv a]
  rfl

theorem FactorizationDatum.factorizationL_le_normalizer_factorizationD
    (f : FactorizationDatum p α θ q M Q₀) :
    factorizationL θ Q₀ ≤ Subgroup.normalizer (factorizationD α θ q Q₀ : Set G) := by
  obtain ⟨-, -, -, ⟨hL_inv, -, hL_cop, hL_bal⟩, -, -, -⟩ := FactorizationDatum.basic_subgroups f
  have := nontrivial_of_factorizationDatum f
  have := f.solvable.isElementaryAbelian
  have hgen : factorizationL θ Q₀ ≤ ⨆ (B : Subgroup A) (_ : B.index = p),
      fixedInBySubgroup α (factorizationL θ Q₀) B := by
    have hmap := congrArg (Subgroup.map (factorizationL θ Q₀).subtype)
      (iSup_fixedBySubgroup_index_eq_top p f.solvable.prime
        (restrictAction α (factorizationL θ Q₀) hL_inv)
        (f.solvable.prime.coprime_iff_not_dvd.mp hL_cop))
    simp only [Subgroup.map_iSup, fixedBySubgroup_restrictAction_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype] at hmap
    rw [hmap]
  refine hgen.trans (iSup_le fun B => iSup_le fun hB => ?_)
  obtain ⟨_, hDKB, _, _, _, _⟩ := factorizationD_eq_iSup_conjugate f B hB
  obtain ⟨_, _, hCBnorm, _⟩ := FactorizationDatum.hyperplaneCore_spec f B hB
  have hcommon : fixedInBySubgroup α (factorizationL θ Q₀) B ≤ commonSignalizer θ B := by
    intro x hx
    rw [mem_fixedInBySubgroup] at hx
    simp only [commonSignalizer, Subgroup.mem_iInf]
    exact fun b hb hb1 => hL_bal b hb1 ⟨hx.1, hx.2 b hb⟩
  rw [hDKB]
  exact le_normalizer_iSup_conjugate _ _ _
    (inf_le_left.trans factorizationL_le_normalizer) (hcommon.trans hCBnorm)

private theorem commonSignalizerWhole_eq_mul_and_le_normalizer
    (f : FactorizationDatum p α θ q M Q₀) :
    (commonSignalizerWhole θ : Set G) =
        ((commonSignalizerWhole θ ⊓ factorizationK α θ q : Subgroup G) : Set G) *
        ((commonSignalizerWhole θ ⊓ factorizationL θ Q₀ : Subgroup G) : Set G) ∧
      commonSignalizerWhole θ ≤ Subgroup.normalizer (factorizationG₀ α θ q Q₀ : Set G) := by
  have d := f.solvable
  have := nontrivial_of_factorizationDatum f
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have := d.isElementaryAbelian
  obtain ⟨-, -, -, hLcomp, -, hKN, hleK⟩ := FactorizationDatum.basic_subgroups f
  have hloc := FactorizationDatum.coe_value_eq_mul f a ha
  set C := commonSignalizerWhole θ
  set X := factorizationComplementCore q (θ a)
  set Y := θ a ⊓ factorizationL θ Q₀
  have hXle : X ≤ θ a := Subgroup.map_subtype_le _
  have hXinv : IsInvariant α X := (d.invariant a ha).map_subtype_of_characteristic inferInstance
  have hcop : ¬ p ∣ Nat.card (X ⊓ Y : Subgroup G) := fun h =>
    d.prime.coprime_iff_not_dvd.mp (d.coprime a ha)
      (h.trans (Subgroup.card_dvd_of_le (inf_le_left.trans hXle)))
  have hfixeq : (θ a ⊓ fixedBySubgroup α ⊤ : Subgroup G) = C := by
    simpa [fixedInBySubgroup] using (compatible_values_and_commonSignalizer d).2.2 a ha
  have hprod := mul_inter_actionFixedAll_eq p d.prime
    (CFSG.IsElementaryAbelian.isPGroup p A) α X Y hXinv
    ((d.invariant a ha).inf hLcomp.1) hcop
  rw [← hloc, ← Subgroup.coe_inf, hfixeq] at hprod
  have hPC : X ⊓ fixedBySubgroup α ⊤ ≤ C := (inf_le_inf hXle le_rfl).trans_eq hfixeq
  have hQC : Y ⊓ fixedBySubgroup α ⊤ ≤ C := (inf_le_inf inf_le_left le_rfl).trans_eq hfixeq
  have hPK : X ⊓ fixedBySubgroup α ⊤ ≤ factorizationK α θ q := inf_le_left.trans (hleK a ha)
  have hQL : Y ⊓ fixedBySubgroup α ⊤ ≤ factorizationL θ Q₀ := inf_le_left.trans inf_le_right
  refine ⟨Set.Subset.antisymm (fun g hg => ?_) ?_, fun g hg => ?_⟩
  · rw [hprod] at hg
    obtain ⟨x, hx, y, hy, hxy⟩ := hg
    exact ⟨x, ⟨hPC hx, hPK hx⟩, y, ⟨hQC hy, hQL hy⟩, hxy⟩
  · rintro g ⟨x, hx, y, hy, rfl⟩
    exact C.mul_mem hx.1 hy.1
  · have hg' : g ∈ (C : Set G) := hg
    rw [hprod] at hg'
    obtain ⟨x, hx, y, hy, rfl⟩ := hg'
    have hKG₀ : factorizationK α θ q ≤ Subgroup.normalizer (factorizationG₀ α θ q Q₀ : Set G) :=
      (le_sup_left : factorizationK α θ q ≤ factorizationG₀ α θ q Q₀).trans
        Subgroup.le_normalizer
    refine mul_mem (hKG₀ (hPK hx)) ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hKN (hQC hy), factorizationL_le_normalizer (hQL hy)⟩

theorem FactorizationDatum.compatible_factorizationG₀ (f : FactorizationDatum p α θ q M Q₀) :
    Compatible p α θ (factorizationG₀ α θ q Q₀) := by
  set H : Subgroup G := factorizationG₀ α θ q Q₀
  set K : Subgroup G := factorizationK α θ q with hKdef
  set Q : Subgroup G := factorizationQ Q₀
  obtain ⟨hKQ, -, hHinv, -⟩ := FactorizationDatum.coe_factorizationG₀_eq_mul f
  obtain ⟨-, hnorm⟩ := commonSignalizerWhole_eq_mul_and_le_normalizer f
  obtain ⟨hQne, hQab, hQcompAt, -, -, -, -⟩ := FactorizationDatum.basic_subgroups f
  have hKH : K ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  obtain ⟨d', hfam⟩ := Datum.restrict f.solvable H hHinv
  have hloc' := LocallyComplete.restrict f.solvable f.locally_complete H hHinv
    hnorm
  have hQ'comp : Compatible p (restrictAction α H hHinv) (restrictTheta θ H) (Q.subgroupOf H) := by
    have hmem : (Q.subgroupOf H).map H.subtype ∈
        (fun U : Subgroup H => U.map H.subtype) ''
          {U : Subgroup H | Compatible p (restrictAction α H hHinv) (restrictTheta θ H) U} := by
      rw [hfam, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQH]
      exact ⟨hQcompAt.1, hQH⟩
    obtain ⟨U, hU, hmapU⟩ := hmem
    rwa [Subgroup.map_injective H.subtype_injective hmapU] at hU
  have hcardQ' : Nat.card (Q.subgroupOf H) = Nat.card Q := by
    rw [← Subgroup.card_map_of_injective (K := Q.subgroupOf H) (f := H.subtype)
      H.subtype_injective, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQH]
  have hQ'compAt : CompatibleAt p (restrictAction α H hHinv) (restrictTheta θ H) {q}
      (Q.subgroupOf H) := ⟨hQ'comp, by rw [hcardQ']; exact hQcompAt.2⟩
  have hQ'ab : IsMulCommutative (Q.subgroupOf H) :=
    Subgroup.subgroupOf_isMulCommutative (K := H) (H := Q)
  have hq : q ∈ spectrum (restrictTheta θ H) := by
    have hqdiv : q ∣ Nat.card (Q.subgroupOf H) := by
      rw [hcardQ']
      obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card Q)
        fun h => hQne ((Subgroup.eq_bot_iff_card (H := Q)).mpr h)
      have : r = q := by simpa using hQcompAt.2 r hr hrdvd
      rwa [this] at hrdvd
    exact primeSupported_spectrum_of_compatible d' hQ'comp q f.selected_prime.1 hqdiv
  have hπmem : p ∉ spectrum θ \ {q} := fun h => f.solvable.notMem_spectrum h.1
  have hmap : (completion (primeSubfunctor (restrictAction α H hHinv) (restrictTheta θ H)
      (spectrum (restrictTheta θ H) \ {q}))).map H.subtype = K := by
    rw [hKdef, factorizationK, completion, completion]
    simp only [Subgroup.map_iSup]
    refine iSup_congr fun a => iSup_congr fun ha => ?_
    rw [← primeSubfunctor_diff_singleton_eq ha (spectrum_restrictTheta_subset θ H),
      map_primeSubfunctor_restrict f.solvable H hHinv hnorm (spectrum θ \ {q})
        hπmem a ha]
    have hleK : primeSubfunctor α θ (spectrum θ \ {q}) a ≤ K :=
      le_trans (le_iSup (fun _ : a ≠ 1 => primeSubfunctor α θ (spectrum θ \ {q}) a) ha)
        (le_iSup (fun a' => ⨆ (_ : a' ≠ 1), primeSubfunctor α θ (spectrum θ \ {q}) a') a)
    exact inf_eq_left.mpr (hleK.trans hKH)
  have hprod : (completion (primeSubfunctor (restrictAction α H hHinv) (restrictTheta θ H)
      (spectrum (restrictTheta θ H) \ {q})) : Set H) * (Q.subgroupOf H : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : (x : G) ∈ (K : Set G) * (Q : Set G) := by rw [← hKQ]; exact x.2
    obtain ⟨k, hk, q', hq', hkq⟩ := hx
    rw [← hmap] at hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    exact ⟨k', hk', ⟨q', hQH hq'⟩, hq', Subtype.ext hkq⟩
  obtain ⟨hcomplete', htop, -⟩ := isComplete_of_abelian_hall_product p (restrictAction α H hHinv)
    (restrictTheta θ H) d' hloc' f.rank_three q hq (Q.subgroupOf H) hQ'compAt hQ'ab hprod
  have hmem : (completion (restrictTheta θ H)).map H.subtype ∈
      (fun U : Subgroup H => U.map H.subtype) ''
        {U : Subgroup H | Compatible p (restrictAction α H hHinv) (restrictTheta θ H) U} :=
    ⟨completion (restrictTheta θ H), hcomplete', rfl⟩
  rw [hfam, htop, Subgroup.map_top, Subgroup.range_subtype] at hmem
  exact hmem.1

end CFSG.SolvableSignalizer
