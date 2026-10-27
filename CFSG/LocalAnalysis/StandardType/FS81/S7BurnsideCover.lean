module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem exists_normal_odd_cover_of_selfNormalizing {X : Type} [Group X] [Finite X]
    {S P : Subgroup X} {σ : X} (hPS : P ≤ S) (hP : IsPGroup 2 P) (hσP : σ ∈ P)
    (hSσ : ∀ s ∈ S, s * σ = σ * s)
    (hPP : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ)
    (hN : ∀ x ∈ S, x ∈ Subgroup.normalizer (P : Set X) → x ∈ P) :
    ∃ M : Subgroup X, M ≤ S ∧ (M.subgroupOf S).Normal ∧ Subgroup.zpowers σ ≤ M ∧
      (∃ m : ℕ, Odd m ∧ Nat.card M = Nat.card (Subgroup.zpowers σ) * m) ∧ S ≤ M ⊔ P := by
  classical
  let Z : Subgroup X := Subgroup.zpowers σ
  have hZ_le_S : Z ≤ S := Subgroup.zpowers_le.mpr (hPS hσP)
  let Z' : Subgroup S := Z.subgroupOf S
  have hσ_cent : σ ∈ Subgroup.centralizer (S : Set X) :=
    Subgroup.mem_centralizer_iff.mpr hSσ
  have hZ_cent : Z ≤ Subgroup.centralizer (S : Set X) := Subgroup.zpowers_le.mpr hσ_cent
  have hZ'_normal : Z'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnZ : (n : X) ∈ Z := hn
    have h_comm : (g : X) * (n : X) = (n : X) * (g : X) :=
      (Subgroup.mem_centralizer_iff.mp (hZ_cent hnZ)) g g.2
    have h_eq : (g : X) * (n : X) * (g : X)⁻¹ = (n : X) := by
      rw [h_comm]
      group
    rw [Subgroup.mem_subgroupOf]
    change (g : X) * (n : X) * (g : X)⁻¹ ∈ Z
    rw [h_eq]
    exact hnZ
  let Q : Type := S ⧸ Z'
  let π : S →* Q := QuotientGroup.mk' Z'
  have hπ_surj : Function.Surjective π := QuotientGroup.mk'_surjective Z'
  have hπ_ker : π.ker = Z' := QuotientGroup.ker_mk' Z'
  let P' : Subgroup S := P.subgroupOf S
  let Pbar : Subgroup Q := P'.map π
  have hZ'leP' : Z' ≤ P' := Subgroup.subgroupOf_mono S (Subgroup.zpowers_le.mpr hσP)
  have hP'_pgroup : IsPGroup 2 P' :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  have hPbar_pgroup : IsPGroup 2 Pbar := hP'_pgroup.map π
  have hPbar_comm_x : ∀ x ∈ P', ∀ y ∈ P', π x * π y = π y * π x := by
    intro x hx y hy
    have hcomm : x * y * x⁻¹ * y⁻¹ ∈ Z' := by
      rw [Subgroup.mem_subgroupOf]
      exact hPP x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy)
    have hπcomm : π (x * y * x⁻¹ * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (x * y * x⁻¹ * y⁻¹)).mpr hcomm
    have h : π x * π y * (π x)⁻¹ * (π y)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hπcomm
    calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
      _ = 1 * (π y * π x) := by rw [h]
      _ = π y * π x := by group
  have hPbar_comm : ∀ a b : Pbar, a * b = b * a := by
    intro a b
    obtain ⟨x, hxP', hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hyP', hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← hxa, ← hyb]
    exact hPbar_comm_x x hxP' y hyP'
  have hπ_mem_Pbar : ∀ x : S, π x ∈ Pbar ↔ x ∈ P' := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hx
      have hx_p_inv : π (x * p⁻¹) = 1 := by
        rw [map_mul, map_inv, hpx]
        exact mul_inv_cancel (π x)
      have hmem : x * p⁻¹ ∈ Z' := (QuotientGroup.eq_one_iff (x * p⁻¹)).mp hx_p_inv
      have h_eq : x = (x * p⁻¹) * p := by group
      rw [h_eq]
      exact P'.mul_mem (hZ'leP' hmem) hp
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hNQ : Subgroup.normalizer (Pbar : Set Q) ≤ Pbar := by
    intro q hq
    obtain ⟨x, rfl⟩ := hπ_surj q
    have hx_norm_P' : x ∈ Subgroup.normalizer (P' : Set S) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [← hπ_mem_Pbar h, ← hπ_mem_Pbar (x * h * x⁻¹)]
      have hq' := (Subgroup.mem_normalizer_iff.mp hq) (π h)
      rw [map_mul, map_mul, map_inv]
      exact hq'
    have hx_norm_P : (x : X) ∈ Subgroup.normalizer (P : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      by_cases hS : h ∈ S
      · have hS' := (Subgroup.mem_normalizer_iff.mp hx_norm_P') ⟨h, hS⟩
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hS'
        simpa using hS'
      · have hP' : h ∉ P := fun hp => hS (hPS hp)
        have hx_inv_notS : (x : X) * h * (x : X)⁻¹ ∉ S := by
          intro hmem
          have h_eq : h = (x : X)⁻¹ * ((x : X) * h * (x : X)⁻¹) * (x : X) := by group
          have hh : h ∈ S := by
            rw [h_eq]
            exact S.mul_mem (S.mul_mem (S.inv_mem x.2) hmem) x.2
          exact hS hh
        have hxP : (x : X) * h * (x : X)⁻¹ ∉ P := fun hp => hx_inv_notS (hPS hp)
        exact iff_of_false hP' hxP
    have hxP : (x : X) ∈ P := hN (x : X) x.2 hx_norm_P
    exact (hπ_mem_Pbar x).mpr (Subgroup.mem_subgroupOf.mpr hxP)
  have hPbar_normalizer_eq : Subgroup.normalizer (Pbar : Set Q) = Pbar :=
    le_antisymm hNQ Pbar.le_normalizer
  obtain ⟨Q₂, hPbar_le_Q₂⟩ := hPbar_pgroup.exists_le_sylow
  have hQ₂_nilpotent : Group.IsNilpotent (Q₂ : Subgroup Q) :=
    IsPGroup.isNilpotent Q₂.isPGroup'
  have hnc : NormalizerCondition (Q₂ : Subgroup Q) := normalizerCondition_of_isNilpotent
  have hPbar_eq_Q₂ : Pbar = Q₂ := by
    by_contra hne
    have hlt : Pbar.subgroupOf Q₂ < ⊤ := by
      refine lt_of_le_of_ne le_top ?_
      intro htop
      have hle : Q₂ ≤ Pbar := by
        intro q hq
        have : (⟨q, hq⟩ : Q₂) ∈ Pbar.subgroupOf Q₂ := by rw [htop]; trivial
        rwa [Subgroup.mem_subgroupOf] at this
      exact hne (le_antisymm hPbar_le_Q₂ hle)
    have hnorm : Subgroup.normalizer (Pbar.subgroupOf Q₂) = Pbar.subgroupOf Q₂ := by
      rw [← Subgroup.subgroupOf_normalizer_eq hPbar_le_Q₂, hPbar_normalizer_eq]
    have htop' : Pbar.subgroupOf Q₂ = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hnorm
    exact hlt.ne htop'
  let PbarSylow : Sylow 2 Q := Q₂
  have hPbarSylow_coe : (↑PbarSylow : Subgroup Q) = Pbar := by
    change Q₂ = Pbar
    exact hPbar_eq_Q₂.symm
  have hPbar_le_cent : Pbar ≤ Subgroup.centralizer (Pbar : Set Q) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hPbar_comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hcen : Subgroup.normalizer (↑PbarSylow : Set Q) ≤
      Subgroup.centralizer (↑PbarSylow : Set Q) := by
    have hset : (↑PbarSylow : Set Q) = (Pbar : Set Q) :=
      congrArg (fun H : Subgroup Q => (H : Set Q)) hPbarSylow_coe
    rw [hset]
    exact hNQ.trans hPbar_le_cent
  let Kbar : Subgroup Q := (MonoidHom.transferSylow PbarSylow hcen).ker
  have hKbar_normal : Kbar.Normal := inferInstance
  have hKbar_compl : Kbar.IsComplement' (↑PbarSylow : Subgroup Q) :=
    MonoidHom.ker_transferSylow_isComplement' PbarSylow hcen
  have hKbar_sup : Kbar ⊔ Pbar = ⊤ := by
    have h := hKbar_compl.sup_eq_top
    rwa [hPbarSylow_coe] at h
  let M' : Subgroup S := Kbar.comap π
  have hM'_normal : M'.Normal := hKbar_normal.comap π
  let M : Subgroup X := M'.map S.subtype
  have hM_le_S : M ≤ S := Subgroup.map_subtype_le M'
  have hM_subgroupOf : M.subgroupOf S = M' := by
    change (M'.map S.subtype).comap S.subtype = M'
    rw [Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  have hM_normal : (M.subgroupOf S).Normal := by
    rw [hM_subgroupOf]
    exact hM'_normal
  have hZ_le_M : Subgroup.zpowers σ ≤ M := by
    intro z hz
    have hzZ : z ∈ Z := hz
    have hzS : z ∈ S := hZ_le_S hzZ
    have hzZ' : (⟨z, hzS⟩ : S) ∈ Z' := by
      rw [Subgroup.mem_subgroupOf]
      exact hzZ
    have hπz : π ⟨z, hzS⟩ = 1 := by
      rw [← hπ_ker] at hzZ'
      exact MonoidHom.mem_ker.mp hzZ'
    have hzM' : (⟨z, hzS⟩ : S) ∈ M' := by
      change (⟨z, hzS⟩ : S) ∈ Kbar.comap π
      rw [Subgroup.mem_comap, hπz]
      exact Kbar.one_mem
    have hz : z = S.subtype ⟨z, hzS⟩ := rfl
    rw [hz]
    exact Subgroup.mem_map_of_mem S.subtype hzM'
  have hZ'leM' : Z' ≤ M' := by
    intro z hz
    change z ∈ Kbar.comap π
    rw [Subgroup.mem_comap]
    rw [show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact Kbar.one_mem
  let π' : M' →* Kbar :=
    { toFun := fun x => ⟨π x.1, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hπ'_surj : Function.Surjective π' := by
    intro k
    obtain ⟨s, hs⟩ := hπ_surj k.1
    have hsmem : s ∈ M' := by
      change s ∈ Kbar.comap π
      rw [Subgroup.mem_comap, hs]
      exact k.2
    exact ⟨⟨s, hsmem⟩, by ext; exact hs⟩
  have hπ'_ker : π'.ker = Z'.subgroupOf M' := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxval : π x.1 = 1 := congrArg Subtype.val hx
      rw [Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff x.1).mp hxval
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff x.1).mpr hx
  have hker_card : Nat.card π'.ker = Nat.card Z' := by
    rw [hπ'_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'leM')
  have hM'_card : Nat.card M' = Nat.card Z' * Nat.card Kbar := by
    have h := Subgroup.card_ker_mul_card_of_surjective hπ'_surj
    rw [hker_card] at h
    exact h.symm
  have hcard_M : Nat.card M = Nat.card M' :=
    (Nat.card_congr (Subgroup.equivMapOfInjective M' S.subtype S.subtype_injective)).symm
  have hM_card : Nat.card M = Nat.card Z' * Nat.card Kbar := by
    rw [hcard_M, hM'_card]
  have hZ'_card : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ_le_S)
  have hP'_comap : Pbar.comap π = P' := by
    change (P'.map π).comap π = P'
    rw [Subgroup.comap_map_eq, hπ_ker, sup_eq_left]
    exact hZ'leP'
  have hM'_P'_top : M' ⊔ P' = ⊤ := by
    change Kbar.comap π ⊔ P' = ⊤
    rw [← hP'_comap]
    rw [Subgroup.comap_sup_eq π Kbar Pbar hπ_surj, hKbar_sup]
    exact Subgroup.comap_top π
  have hS_le_MP : S ≤ M ⊔ P := by
    intro s hs
    have hs_top : (⟨s, hs⟩ : S) ∈ M' ⊔ P' := by
      rw [hM'_P'_top]
      trivial
    have hs_mem : (⟨s, hs⟩ : S) ∈ (M ⊔ P).subgroupOf S := by
      rw [Subgroup.subgroupOf_sup hM_le_S hPS, hM_subgroupOf]
      exact hs_top
    rwa [Subgroup.mem_subgroupOf] at hs_mem
  refine ⟨M, hM_le_S, hM_normal, hZ_le_M, ?_, hS_le_MP⟩
  refine ⟨Nat.card Kbar, ?_, ?_⟩
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    have hKbar_index : (↑PbarSylow : Subgroup Q).index = Nat.card Kbar :=
      hKbar_compl.index_eq_card
    rw [← hKbar_index]
    exact PbarSylow.not_dvd_index
  · rw [hM_card, hZ'_card]

end CFSG.StandardType.FrameRoute.FS81

end
