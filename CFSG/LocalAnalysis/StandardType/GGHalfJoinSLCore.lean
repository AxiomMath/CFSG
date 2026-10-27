module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSLConj
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSLPerf
public import CFSG.LocalAnalysis.StandardType.GGHalfFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private theorem sigmaPerm_mul_self (m : ℕ) (hm : 1 ≤ m) : sigmaPerm m * sigmaPerm m = 1 := by
  ext i
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  by_cases h0 : i = 0
  · rw [h0, sigmaPerm_apply_zero m hm, sigmaPerm_apply_two m hm]
  by_cases h1 : i = 1
  · rw [h1, sigmaPerm_apply_one m hm, sigmaPerm_apply_three m hm]
  by_cases h2 : i = 2
  · rw [h2, sigmaPerm_apply_two m hm, sigmaPerm_apply_zero m hm]
  by_cases h3 : i = 3
  · rw [h3, sigmaPerm_apply_three m hm, sigmaPerm_apply_one m hm]
  · rw [sigmaPerm_apply_of_fixed m h0 h1 h2 h3, sigmaPerm_apply_of_fixed m h0 h1 h2 h3]

private theorem commutator_map_conj {G : Type*} [Group G] {J : Subgroup G}
    (hJ : commutator ↥J = ⊤) (g : G) :
    commutator ↥(J.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let e : ↥J ≃* ↥(J.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulEquiv.injective _)
  have hmap : Subgroup.map e.toMonoidHom (commutator ↥J) =
      commutator ↥(J.map (MulAut.conj g).toMonoidHom) := by
    simp only [commutator]
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  rw [hJ, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  exact hmap.symm

theorem GGHalfJoin.fusion_core {m : ℕ} (hm : 1 ≤ m)
    {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ha : orderOf a = 3) (hs : GGHalf.supp a = 2)
    {J T : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)} (hJ : commutator ↥J = ⊤)
    (hJa : J ≤ Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)))
    (hTJ : T ≤ J) (hT : IsElemAbelian 3 T) (hTcard : Nat.card ↥T = 3 ^ ((m + 1) / 2)) :
    ∃ n' : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      n' ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ T : Subgroup _) : Set _) ∧
        n' * a * n'⁻¹ ∈ T ∧ n' * a * n'⁻¹ ≠ 1 := by
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  obtain ⟨A₁, hA₁⟩ := GGHalfJoin.exists_conj_omegaBlock_of_supp_two ha3 hs
  set ω₀ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
    omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ with hω₀
  set J₁ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :=
    J.map (MulAut.conj A₁⁻¹).toMonoidHom with hJ₁
  set T₁ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :=
    T.map (MulAut.conj A₁⁻¹).toMonoidHom with hT₁
  set T₀ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :=
    (halfTorus m).map (slLower2Hom m) with hT₀
  have hJ₁perf : commutator ↥J₁ = ⊤ := by
    rw [hJ₁]
    exact commutator_map_conj hJ A₁⁻¹
  have hJ₁comm : ∀ g ∈ J₁, g * ω₀ = ω₀ * g := by
    intro g hg
    rw [hJ₁] at hg
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hg
    have hja : j * a = a * j := Subgroup.mem_centralizer_singleton_iff.mp (hJa hj)
    have hconj₁ : (MulAut.conj A₁⁻¹) a = ω₀ := by
      rw [MulAut.conj_apply, inv_inv]
      exact hA₁
    calc (MulAut.conj A₁⁻¹) j * ω₀
        = (MulAut.conj A₁⁻¹) j * (MulAut.conj A₁⁻¹) a := by rw [hconj₁]
      _ = (MulAut.conj A₁⁻¹) (j * a) := by rw [map_mul]
      _ = (MulAut.conj A₁⁻¹) (a * j) := by rw [hja]
      _ = (MulAut.conj A₁⁻¹) a * (MulAut.conj A₁⁻¹) j := by rw [map_mul]
      _ = ω₀ * (MulAut.conj A₁⁻¹) j := by rw [hconj₁]
  have hJ₁le : J₁ ≤ (slLower2Hom m).range :=
    GGHalfJoin.le_range_slLower2Hom_of_perfect_of_commute hJ₁perf hJ₁comm
  have hT₁J₁ : T₁ ≤ J₁ := by
    rw [hT₁, hJ₁]
    exact Subgroup.map_mono hTJ
  have hT₁le : T₁ ≤ (slLower2Hom m).range := le_trans hT₁J₁ hJ₁le
  have hT₁elem : IsElemAbelian 3 T₁ := by
    rw [hT₁]
    exact isElemAbelian_map_conj hT A₁⁻¹
  have hT₁card : Nat.card ↥T₁ = 3 ^ ((m + 1) / 2) := by
    rw [hT₁, Subgroup.card_map_of_injective (MulEquiv.injective _), hTcard]
  set T'' : Subgroup (SpecialLinearGroup (Fin (m + 1)) F2) := T₁.comap (slLower2Hom m) with hT''
  have hT''map : T''.map (slLower2Hom m) = T₁ := by
    rw [hT'', Subgroup.map_comap_eq_self hT₁le]
  have hT''card : Nat.card ↥T'' = 3 ^ ((m + 1) / 2) := by
    have h1 : Nat.card ↥(T''.map (slLower2Hom m)) = Nat.card ↥T'' :=
      Subgroup.card_map_of_injective (slLower2Hom_injective m)
    rw [hT''map, hT₁card] at h1
    exact h1.symm
  have hT''comm : ∀ x ∈ T'', ∀ y ∈ T'', x * y = y * x := by
    intro x hx y hy
    have hx' : slLower2Hom m x ∈ T₁ := by
      rw [← hT''map]; exact Subgroup.mem_map_of_mem _ hx
    have hy' : slLower2Hom m y ∈ T₁ := by
      rw [← hT''map]; exact Subgroup.mem_map_of_mem _ hy
    have h := hT₁elem.1.is_comm.comm ⟨slLower2Hom m x, hx'⟩ ⟨slLower2Hom m y, hy'⟩
    apply slLower2Hom_injective m
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h
  have hT''3 : ∀ x ∈ T'', x ^ 3 = 1 := by
    intro x hx
    have hx' : slLower2Hom m x ∈ T₁ := by
      rw [← hT''map]; exact Subgroup.mem_map_of_mem _ hx
    apply slLower2Hom_injective m
    rw [map_pow, map_one]
    exact hT₁elem.2 _ hx'
  obtain ⟨A'', hA''⟩ := exists_conj_into_halfTorus (n := m) (T'' : Set _) hT''comm hT''3
  have hle : T''.map (MulAut.conj A''⁻¹).toMonoidHom ≤ halfTorus m := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have h := hA'' x hx
    show A''⁻¹ * x * A''⁻¹⁻¹ ∈ halfTorus m
    rwa [inv_inv]
  have hcard_le : Nat.card ↥(halfTorus m) ≤
      Nat.card ↥(T''.map (MulAut.conj A''⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hT''card, card_halfTorus m]
  have heq : T''.map (MulAut.conj A''⁻¹).toMonoidHom = halfTorus m :=
    Subgroup.eq_of_le_of_card_ge hle hcard_le
  set c'' : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := slLower2Hom m A'' with hc''
  have hcomp : (slLower2Hom m).comp (MulAut.conj A''⁻¹).toMonoidHom =
      (MulAut.conj c''⁻¹).toMonoidHom.comp (slLower2Hom m) := by
    refine MonoidHom.ext fun x => ?_
    show slLower2Hom m (A''⁻¹ * x * A''⁻¹⁻¹) = c''⁻¹ * slLower2Hom m x * c''⁻¹⁻¹
    simp only [hc'', map_mul, map_inv, inv_inv]
  have hc''conj : T₁.map (MulAut.conj c''⁻¹).toMonoidHom = T₀ := by
    have h1 : (T''.map (MulAut.conj A''⁻¹).toMonoidHom).map (slLower2Hom m) =
        (halfTorus m).map (slLower2Hom m) := by rw [heq]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hT''map] at h1
    rw [hT₀]
    exact h1
  set A : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := A₁ * c'' with hA
  have hc''mem : c'' ∈ slOn (m + 1 + 1 + 1) {i | 2 ≤ i.val} := by
    rw [← range_slLower2Hom m]
    exact ⟨A'', hc''.symm⟩
  have hc''commω : c'' * ω₀ = ω₀ * c'' := by
    have hk : (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)).castSucc ∉
          {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} ∧
        (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)).succ ∉
          {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val} := by
      constructor
      · simp only [Set.mem_setOf_eq, not_le, Fin.val_castSucc]; omega
      · simp only [Set.mem_setOf_eq, not_le, Fin.val_succ]; omega
    rw [hω₀]
    exact (commute_omegaBlock_slOn hk hc''mem).symm
  have hconjA : (MulAut.conj A⁻¹) a = ω₀ := by
    rw [MulAut.conj_apply, inv_inv, hA]
    calc (A₁ * c'')⁻¹ * a * (A₁ * c'')
        = c''⁻¹ * (A₁⁻¹ * a * A₁) * c'' := by group
      _ = c''⁻¹ * ω₀ * c'' := by rw [hA₁]
      _ = ω₀ := by
          calc c''⁻¹ * ω₀ * c'' = c''⁻¹ * (ω₀ * c'') := by rw [mul_assoc]
            _ = c''⁻¹ * (c'' * ω₀) := by rw [← hc''commω]
            _ = (c''⁻¹ * c'') * ω₀ := by rw [mul_assoc]
            _ = ω₀ := by rw [inv_mul_cancel, one_mul]
  have hAT : T.map (MulAut.conj A⁻¹).toMonoidHom = T₀ := by
    have hAeq : (MulAut.conj A⁻¹).toMonoidHom =
        (MulAut.conj c''⁻¹).toMonoidHom.comp (MulAut.conj A₁⁻¹).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      show A⁻¹ * x * A⁻¹⁻¹ = c''⁻¹ * (A₁⁻¹ * x * A₁⁻¹⁻¹) * c''⁻¹⁻¹
      rw [hA]
      group
    rw [hAeq, ← Subgroup.map_map, ← hT₁]
    exact hc''conj
  have hconjA' : (MulAut.conj A⁻¹).toMonoidHom a = ω₀ := hconjA
  have h_half : halfTorus (m + 1 + 1) =
      (Subgroup.zpowers a ⊔ T).map (MulAut.conj A⁻¹).toMonoidHom := by
    rw [halfTorus_succ_succ, ← hT₀, ← hAT, Subgroup.map_sup, MonoidHom.map_zpowers,
      hconjA', ← hω₀]
  have hcompA : (MulAut.conj A).toMonoidHom.comp (MulAut.conj A⁻¹).toMonoidHom =
      MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    show A * (A⁻¹ * x * A⁻¹⁻¹) * A⁻¹ = x
    group
  have hsup : (halfTorus (m + 1 + 1)).map (MulAut.conj A).toMonoidHom =
      Subgroup.zpowers a ⊔ T := by
    rw [h_half, Subgroup.map_map, hcompA, Subgroup.map_id]
  set n₀ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := slPerm gf2_two (sigmaPerm m) with hn₀
  have hn₀_sq : n₀ * n₀ = 1 := by
    rw [hn₀, ← map_mul, sigmaPerm_mul_self m hm, map_one]
  have hn₀_inv : n₀⁻¹ = n₀ := inv_eq_of_mul_eq_one_right hn₀_sq
  have hn₀_conj : ∀ t, t ∈ halfTorus (m + 1 + 1) →
      n₀ * t * n₀⁻¹ ∈ halfTorus (m + 1 + 1) := by
    intro t ht
    rw [hn₀]
    exact slPerm_sigma_conj_halfTorus m hm ht
  have hn₀_norm : n₀ ∈ Subgroup.normalizer (halfTorus (m + 1 + 1) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hn₀_conj t
    · intro ht
      have h2 := hn₀_conj (n₀ * t * n₀⁻¹) ht
      have h_eq : n₀ * (n₀ * t * n₀⁻¹) * n₀⁻¹ = t := by
        rw [hn₀_inv]
        calc n₀ * (n₀ * t * n₀) * n₀ = (n₀ * n₀) * t * (n₀ * n₀) := by group
          _ = t := by rw [hn₀_sq, one_mul, mul_one]
      rwa [h_eq] at h2
  have h0 : sigmaPerm m ((⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)).castSucc) =
      (⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
    rw [show (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)) = (0 : Fin (m + 1 + 1)) from Fin.ext rfl,
      Fin.castSucc_zero, sigmaPerm_apply_zero m hm]
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (show (2 : ℕ) < m + 1 + 1 + 1 by omega)]
  have h1 : sigmaPerm m ((⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)).succ) =
      (⟨2, by omega⟩ : Fin (m + 1 + 1)).succ := by
    rw [show (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)) = (0 : Fin (m + 1 + 1)) from Fin.ext rfl,
      Fin.succ_zero_eq_one, sigmaPerm_apply_one m hm]
    apply Fin.ext
    rw [Fin.val_succ, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (show (3 : ℕ) < m + 1 + 1 + 1 by omega)]
  have hω₀_image : n₀ * ω₀ * n₀⁻¹ = slLower2Hom m (omegaBlock m ⟨0, by omega⟩) := by
    rw [hn₀, hω₀, slPerm_conj_omegaBlock (sigmaPerm m) h0 h1, slLower2Hom_omegaBlock]
  have hy : n₀ * ω₀ * n₀⁻¹ ∈ T₀ := by
    rw [hω₀_image, hT₀]
    exact Subgroup.mem_map_of_mem (slLower2Hom m)
      (Subgroup.subset_closure ⟨⟨0, by omega⟩, by norm_num, rfl⟩)
  have hconj_ne : n₀ * ω₀ * n₀⁻¹ ≠ 1 := by
    intro h
    apply omegaBlock_ne_one (m + 1 + 1) ⟨0, Nat.succ_pos _⟩
    rw [← hω₀]
    calc ω₀ = n₀⁻¹ * (n₀ * ω₀ * n₀⁻¹) * n₀ := by group
      _ = n₀⁻¹ * 1 * n₀ := by rw [h]
      _ = 1 := by group
  have ha_eq : a = A * ω₀ * A⁻¹ := by
    rw [← hconjA, MulAut.conj_apply, inv_inv]
    group
  have hkey : (A * n₀ * A⁻¹) * a * (A * n₀ * A⁻¹)⁻¹ =
      A * (n₀ * ω₀ * n₀⁻¹) * A⁻¹ := by
    rw [ha_eq]
    group
  refine ⟨A * n₀ * A⁻¹, ?_, ?_, ?_⟩
  · rw [← hsup]
    exact Subgroup.le_normalizer_map (MulAut.conj A).toMonoidHom
      (Subgroup.mem_map_of_mem _ hn₀_norm)
  · rw [hkey]
    rw [← hAT] at hy
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy
    have hAt : A * (n₀ * ω₀ * n₀⁻¹) * A⁻¹ = t := by
      rw [← hty]
      show A * (A⁻¹ * t * A⁻¹⁻¹) * A⁻¹ = t
      group
    rw [hAt]
    exact ht
  · rw [hkey]
    intro h
    exact hconj_ne (by
      calc n₀ * ω₀ * n₀⁻¹
          = A⁻¹ * (A * (n₀ * ω₀ * n₀⁻¹) * A⁻¹) * A := by group
        _ = A⁻¹ * 1 * A := by rw [h]
        _ = 1 := by group)

end CFSG.StandardType

end
