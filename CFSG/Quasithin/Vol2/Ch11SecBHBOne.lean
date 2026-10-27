module

public import CFSG.Quasithin.Vol2.Ch11SecBHBComm

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem map_inf_eq_of_ker_le {A B : Type*} [Group A] [Group B] (f : A →* B) {P Q : Subgroup A}
    (hP : f.ker ≤ P) : (P ⊓ Q).map f = P.map f ⊓ Q.map f := by
  refine le_antisymm (Subgroup.map_inf_le _ _ _) ?_
  rintro y ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩
  have hk : p⁻¹ * q ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqp, inv_mul_cancel]
  have hqP : q ∈ P := by
    have := P.mul_mem hp (hP hk)
    simpa using this
  exact ⟨q, ⟨hqP, hq⟩, hqp⟩

theorem inf_subgroupOf' {Γ : Type*} [Group Γ] (A B C : Subgroup Γ) :
    (A ⊓ B).subgroupOf C = A.subgroupOf C ⊓ B.subgroupOf C := by
  ext x
  simp [Subgroup.mem_subgroupOf]

variable {G : Type} [Group G] [Finite G]

theorem le_of_isUniqueMaxOver {H T X Y : Subgroup G} (hU : IsUniqueMaxOver H T X)
    (hTY : T ≤ Y) (hYH : Y < H) : Y ≤ X := by
  obtain ⟨N, hN, hYN⟩ := exists_isMaxSubgroupIn hYH
  rw [← (isUniqueMaxOver_iff.mp hU).2.2 N hN (hTY.trans hYN)]
  exact hYN

theorem solvRad_le_of_isUniqueMaxOver {H T X : Subgroup G} (hU : IsUniqueMaxOver H T X)
    (hT2 : IsPGroup 2 T) (hns : ¬ Group.IsSolvable ↥H) : solvRad H ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := isUniqueMaxOver_iff.mp hU
  have hTH : T ≤ H := hX.2.1.trans hX.1.le
  have hle : solvRad H ⊔ T ≤ H := sup_le (solvRad_le H) hTH
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    apply hns
    have hTn : T ≤ Subgroup.normalizer (solvRad H : Set G) :=
      hTH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (solvRad_le H)).mp
        (solvRad_normal H))
    have : Group.IsSolvable ↥(solvRad H) := solvRad_isSolvable H
    have : Group.IsSolvable ↥T := by
      have := hT2.isNilpotent
      infer_instance
    have h := A3.isSolvable_sup_of_le_normalizer (M := solvRad H) (N := T) hTn
    rw [heq] at h
    exact h
  · exact le_sup_left.trans (le_of_isUniqueMaxOver hU le_sup_right hlt)

theorem solvRad_le_kerIn {H T X : Subgroup G} (hU : IsUniqueMaxOver H T X)
    (hT2 : IsPGroup 2 T) (hns : ¬ Group.IsSolvable ↥H) : solvRad H ≤ kerIn X H := by
  intro x hx
  show ∀ b ∈ H, b * x * b⁻¹ ∈ X
  intro b hb
  exact solvRad_le_of_isUniqueMaxOver hU hT2 hns
    (conj_mem_solvRad (Subgroup.le_normalizer hb) hx)

theorem isPGroup_commutator_case_one {H T X K : Subgroup G} (hU : IsUniqueMaxOver H T X)
    (hT2 : IsPGroup 2 T) (hns : ¬ Group.IsSolvable ↥H) (hKc : K ∈ cComp H)
    (hJ : kerIn X H = pCoreOf 2 H) (hXK : IsPGroup 2 ↥⁅X ⊓ K, X ⊓ K⁆) :
    IsPGroup 2 ↥⁅conjClosure (X ⊓ K) T ⊔ pCoreOf 2 H, conjClosure (X ⊓ K) T ⊔ pCoreOf 2 H⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := isUniqueMaxOver_iff.mp hU
  have hXH : X ≤ H := hX.1.le
  have hTX : T ≤ X := hX.2.1
  have hTH : T ≤ H := hTX.trans hXH
  have hRX : solvRad H ≤ X := solvRad_le_of_isUniqueMaxOver hU hT2 hns
  have hRO : solvRad H ≤ pCoreOf 2 H := hJ ▸ solvRad_le_kerIn hU hT2 hns
  have hR2 : IsPGroup 2 ↥(solvRad H) := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hRO
  set π := QuotientGroup.mk' (CFSG.solvableRadical ↥H) with hπdef
  have hker : π.ker = CFSG.solvableRadical ↥H := QuotientGroup.ker_mk' _
  have hRmap : (CFSG.solvableRadical ↥H).map H.subtype = solvRad H :=
    (solvRad_eq_map_solvableRadical H).symm
  have hmemR : ∀ x : ↥H, x ∈ π.ker → (x : G) ∈ solvRad H := fun x hx => by
    rw [← hRmap]
    exact ⟨x, hker ▸ hx, rfl⟩
  have hker2 : IsPGroup 2 ↥π.ker := by
    have h1 := (hR2.comap_of_injective H.subtype H.subtype_injective)
    refine h1.to_le fun x hx => ?_
    exact hmemR x hx
  have hkerX : π.ker ≤ X.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRX (hmemR x hx))
  have hcomp : ∀ s ∈ T, CFSG.IsComponent (((cjSub s K).subgroupOf H).map π) := by
    intro s hs
    have h1 : cjSub s K ∈ cComp H := by
      have := cComp_map_mulEquiv (MulAut.conj s) hKc
      rwa [map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hTH hs))] at this
    have h3 := map_mem_cComp_top π (QuotientGroup.mk'_surjective _)
      (by rw [hker]; exact A3.solvableRadical_isSolvable) (subgroupOf_mem_cComp h1)
    exact isComponent_of_mem_cComp_top (A3.solvableRadical_quotient_eq_bot ↥H) h3
  set Abar : G → Subgroup (↥H ⧸ CFSG.solvableRadical ↥H) :=
    fun s => ((X ⊓ cjSub s K).subgroupOf H).map π with hAbar
  have hAeq : ∀ s, Abar s = (X.subgroupOf H).map π ⊓ ((cjSub s K).subgroupOf H).map π := by
    intro s
    rw [hAbar]
    dsimp only
    rw [inf_subgroupOf', map_inf_eq_of_ker_le π hkerX]
  set 𝒜 : Set (Subgroup (↥H ⧸ CFSG.solvableRadical ↥H)) := {A | ∃ s ∈ T, A = Abar s} with h𝒜
  have hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A = B ∨ ⁅A, B⁆ = ⊥ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    rcases CFSG.LocalCores.distinct_components_commute (hcomp s hs) (hcomp s' hs') with h | h
    · left
      rw [hAeq, hAeq, h]
    · right
      rw [eq_bot_iff, ← h]
      exact Subgroup.commutator_mono ((hAeq s).le.trans inf_le_right)
        ((hAeq s').le.trans inf_le_right)
  have h2A : ∀ A ∈ 𝒜, IsPGroup 2 ↥⁅A, A⁆ := by
    rintro _ ⟨s, hs, rfl⟩
    have hsX : s ∈ X := hTX hs
    have he : X ⊓ cjSub s K = cjSub s (X ⊓ K) := by
      unfold cjSub
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective,
        map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hsX)]
    have h1 : IsPGroup 2 ↥⁅X ⊓ cjSub s K, X ⊓ cjSub s K⁆ := by
      rw [he, cjSub, ← Subgroup.map_commutator]
      exact hXK.map _
    have hle : X ⊓ cjSub s K ≤ H := inf_le_left.trans hXH
    have h2 : IsPGroup 2 ↥⁅(X ⊓ cjSub s K).subgroupOf H, (X ⊓ cjSub s K).subgroupOf H⁆ := by
      have h3 : ⁅(X ⊓ cjSub s K).subgroupOf H, (X ⊓ cjSub s K).subgroupOf H⁆.map H.subtype =
          ⁅X ⊓ cjSub s K, X ⊓ cjSub s K⁆ := by
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle]
      have h4 := (h3 ▸ h1 : IsPGroup 2 ↥(⁅(X ⊓ cjSub s K).subgroupOf H,
        (X ⊓ cjSub s K).subgroupOf H⁆.map H.subtype)).comap_of_injective H.subtype
        H.subtype_injective
      rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h4
    show IsPGroup 2 ↥⁅((X ⊓ cjSub s K).subgroupOf H).map π, ((X ⊓ cjSub s K).subgroupOf H).map π⁆
    rw [← Subgroup.map_commutator]
    exact h2.map π
  have hY2 : IsPGroup 2 ↥⁅sSup 𝒜, sSup 𝒜⁆ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (commutator_sSup_le_pCoreOf hcomm h2A)
  set N := conjClosure (X ⊓ K) T ⊔ pCoreOf 2 H with hNdef
  have hNH : N ≤ H := sup_le (conjClosure_le fun t ht z hz =>
    H.mul_mem (H.mul_mem (hTH ht) (hXH hz.1)) (H.inv_mem (hTH ht)))
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hOR : pCoreOf 2 H ≤ solvRad H := by
    refine le_solvRad (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) ?_
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
    infer_instance
  have hNW : ∀ x : ↥H, (x : G) ∈ N → π x ∈ sSup 𝒜 := by
    set W := ((sSup 𝒜).comap π).map H.subtype with hWdef
    have hgen : N ≤ W := by
      refine sup_le (conjClosure_le fun t ht z hz => ?_) fun y hy => ?_
      · have hy : t * z * t⁻¹ ∈ H := H.mul_mem (H.mul_mem (hTH ht) (hXH hz.1)) (H.inv_mem (hTH ht))
        refine ⟨⟨_, hy⟩, ?_, rfl⟩
        have hmem : (⟨_, hy⟩ : ↥H) ∈ (X ⊓ cjSub t K).subgroupOf H := by
          rw [Subgroup.mem_subgroupOf]
          refine ⟨X.mul_mem (X.mul_mem (hTX ht) hz.1) (X.inv_mem (hTX ht)), ?_⟩
          show t * z * t⁻¹ ∈ cjSub t K
          rw [mem_cjSub]
          simpa [mul_assoc] using hz.2
        exact (le_sSup ⟨t, ht, rfl⟩ : Abar t ≤ sSup 𝒜) ⟨_, hmem, rfl⟩
      · have hyH : y ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hy
        refine ⟨⟨y, hyH⟩, ?_, rfl⟩
        have hk : (⟨y, hyH⟩ : ↥H) ∈ π.ker := by
          rw [hker]
          have h1 : y ∈ (CFSG.solvableRadical ↥H).map H.subtype := hRmap ▸ hOR hy
          obtain ⟨y', hy', hyy'⟩ := h1
          rwa [show (⟨y, hyH⟩ : ↥H) = y' from Subtype.ext hyy'.symm]
        show π _ ∈ sSup 𝒜
        rw [hk]
        exact Subgroup.one_mem _
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := hgen hx
    rwa [show x = x' from Subtype.ext hxx'.symm]
  have hN'A : (N.subgroupOf H).map π ≤ sSup 𝒜 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNW x (Subgroup.mem_subgroupOf.mp hx)
  have h1 : IsPGroup 2 ↥(⁅N.subgroupOf H, N.subgroupOf H⁆.map π) := by
    rw [Subgroup.map_commutator]
    exact hY2.to_le (Subgroup.commutator_mono hN'A hN'A)
  have h2 : IsPGroup 2 ↥⁅N.subgroupOf H, N.subgroupOf H⁆ :=
    (h1.comap_of_ker_isPGroup π hker2).to_le (Subgroup.le_comap_map π _)
  have heq : ⁅N, N⁆ = ⁅N.subgroupOf H, N.subgroupOf H⁆.map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hNH]
  rw [heq]
  exact h2.map H.subtype

end CFSG.Quasithin.Vol2.Ch11.SecB
