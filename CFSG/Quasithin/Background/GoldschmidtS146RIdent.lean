module

public import CFSG.Quasithin.Background.GoldschmidtS146RAux
public import CFSG.Quasithin.EmptyFaithful.S146D1

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem pCore_two_eq_ker' {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (g : G →* S) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : CFSG.pCore 2 G = g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hker⟩)
  have hP : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have hN : ((CFSG.pCore 2 G).map g).Normal := Subgroup.Normal.map inferInstance g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 G).map g) with h | h
  · intro x hx
    have : g x ∈ (CFSG.pCore 2 G).map g := ⟨x, hx, rfl⟩
    rw [h] at this
    exact this
  · exfalso
    have h2 : IsPGroup 2 S := by
      have := hP.map g
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    have := h2.isNilpotent
    obtain ⟨a, b, hab⟩ := hS
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

noncomputable def modO2Equiv' {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (g : G →* S) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : (G ⧸ CFSG.pCore 2 G) ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq (pCore_two_eq_ker' hS g hg hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)

section Index

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_of_card {T Y H₂ : Subgroup G} (hTH : T ≤ H₂) (hYH : Y ≤ H₂)
    (hsup : H₂ = T ⊔ Y) (hnorm : (Y.subgroupOf H₂).Normal) {a : ℕ}
    (hcard : Nat.card ↥Y = a * Nat.card ↥(T ⊓ Y)) : T.relIndex H₂ = a := by
  set N : Subgroup ↥H₂ := Y.subgroupOf H₂ with hN
  set Tt : Subgroup ↥H₂ := T.subgroupOf H₂ with hTt
  have hsupN : Tt ⊔ N = ⊤ := by
    rw [hTt, hN, ← Subgroup.subgroupOf_sup hTH hYH, ← hsup, Subgroup.subgroupOf_self]
  have h1 : N.relIndex (Tt ⊔ N) = N.relIndex Tt := Subgroup.relIndex_sup_right Tt N
  rw [hsupN, Subgroup.relIndex_top_right] at h1
  have h2 : N.relIndex Tt * Nat.card ↥(N ⊓ Tt : Subgroup ↥H₂) = Nat.card ↥Tt :=
    Subgroup.relIndex_mul_card N Tt
  have hNT : Nat.card ↥(N ⊓ Tt : Subgroup ↥H₂) = Nat.card ↥(T ⊓ Y) := by
    have : N ⊓ Tt = (Y ⊓ T).subgroupOf H₂ := by
      ext x
      simp [hN, hTt, Subgroup.mem_subgroupOf]
    rw [this, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hYH)).toEquiv
  have hTt' : Nat.card ↥Tt = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hN' : Nat.card ↥N = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  have h3 : Nat.card ↥N * N.index = Nat.card ↥H₂ := Subgroup.card_mul_index N
  have h4 : T.relIndex H₂ * Nat.card ↥(T ⊓ H₂ : Subgroup G) = Nat.card ↥H₂ :=
    Subgroup.relIndex_mul_card T H₂
  rw [inf_of_le_left hTH] at h4
  rw [hNT, hTt'] at h2
  rw [hN', hcard] at h3
  have hidx : N.index ≠ 0 := by
    rw [h1]
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := ↥T)).ne' h2.symm
  have hpos : 0 < N.index * Nat.card ↥(T ⊓ Y) :=
    Nat.mul_pos (Nat.pos_of_ne_zero hidx) Nat.card_pos
  have h5 : T.relIndex H₂ * (N.index * Nat.card ↥(T ⊓ Y)) = a * (N.index * Nat.card ↥(T ⊓ Y)) := by
    have e1 : T.relIndex H₂ * Nat.card ↥T = Nat.card ↥H₂ := h4
    rw [← h3] at e1
    rw [← h1] at h2
    calc T.relIndex H₂ * (N.index * Nat.card ↥(T ⊓ Y))
        = T.relIndex H₂ * Nat.card ↥T := by rw [← h2]
      _ = a * Nat.card ↥(T ⊓ Y) * N.index := e1
      _ = a * (N.index * Nat.card ↥(T ⊓ Y)) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

end Index

section Ident

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem range_toKBar {K K₂ : Subgroup G} (hK₂K : K₂ ≤ K) :
    ((QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp (Subgroup.inclusion hK₂K)).range =
      imgJ K (pCoreOf 2 K) K₂ := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_imgJ.mpr ⟨Subgroup.inclusion hK₂K x, x.2, rfl⟩
  · intro hq
    obtain ⟨h, hh, rfl⟩ := mem_imgJ.mp hq
    exact ⟨⟨h, hh⟩, rfl⟩

theorem isPGroup_ker_toKBar {K K₂ : Subgroup G} (hK₂K : K₂ ≤ K) :
    IsPGroup 2 ((QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp
      (Subgroup.inclusion hK₂K)).ker := by
  set f := (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp (Subgroup.inclusion hK₂K)
    with hf
  have hJ2 : IsPGroup 2 ↥(pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hmem : ∀ x : ↥f.ker, ((K₂.subtype.comp f.ker.subtype) x : G) ∈ pCoreOf 2 K := by
    intro x
    have h1 := x.2
    simp only [hf, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at h1
    exact h1
  let g : ↥f.ker →* ↥(pCoreOf 2 K) := (K₂.subtype.comp f.ker.subtype).codRestrict _ hmem
  have hinj : Function.Injective g := by
    intro x y hxy
    have := congrArg (fun z : ↥(pCoreOf 2 K) => (z : G)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact IsPGroup.of_injective hJ2 g hinj

omit [Finite G] in
theorem isSolvable_imgJ {K Y : Subgroup G} (hYK : Y ≤ K) (h : Group.IsSolvable ↥Y) :
    Group.IsSolvable ↥(imgJ K (pCoreOf 2 K) Y) := by
  set f := (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp (Subgroup.inclusion hYK) with hf
  have h1 : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_surjective (f := f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f)
  rw [hf, range_toKBar hYK] at h1
  exact h1

theorem isSolvable_of_imgJ {K K₂ : Subgroup G} (hK₂K : K₂ ≤ K)
    (h : Group.IsSolvable ↥(imgJ K (pCoreOf 2 K) K₂)) : Group.IsSolvable ↥K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp (Subgroup.inclusion hK₂K)
    with hf
  have hker : Group.IsSolvable ↥f.ker := by
    have := (isPGroup_ker_toKBar hK₂K).isNilpotent
    infer_instance
  have hrange : Group.IsSolvable ↥f.range := by
    rw [hf, range_toKBar hK₂K]
    exact h
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
    rw [Subgroup.range_subtype]
    intro x hx
    simpa using hx)

theorem imgJ_eq_perfectCore {K Y K₂ : Subgroup G} (hK₂Y : K₂ ≤ Y) (hYK : Y ≤ K)
    (hsub : IsSubnormal K₂ Y) (hperf : ⁅K₂, K₂⁆ = K₂) (hns : ¬ Group.IsSolvable ↥K₂)
    {Q : Type} [Group Q] (π : ↥(perfectCore (imgJ K (pCoreOf 2 K) Y)) →* Q)
    (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker) (hQ : IsSimpleGroup Q) :
    imgJ K (pCoreOf 2 K) K₂ = perfectCore (imgJ K (pCoreOf 2 K) Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₂K : K₂ ≤ K := hK₂Y.trans hYK
  have hle : imgJ K (pCoreOf 2 K) K₂ ≤ imgJ K (pCoreOf 2 K) Y := imgJ_mono hK₂Y
  have hperfK : ⁅imgJ K (pCoreOf 2 K) K₂, imgJ K (pCoreOf 2 K) K₂⁆ =
      imgJ K (pCoreOf 2 K) K₂ := by
    have h1 : Group.IsPerfect ↥K₂ := Subgroup.isPerfect_iff.mpr hperf
    have h2 := Group.IsPerfect.range
      ((QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp (Subgroup.inclusion hK₂K))
    rw [range_toKBar hK₂K] at h2
    exact Subgroup.isPerfect_iff.mp h2
  have hKL : imgJ K (pCoreOf 2 K) K₂ ≤ perfectCore (imgJ K (pCoreOf 2 K) Y) :=
    le_perfectCore_of_perfect hle hperfK
  have hsub1 : IsSubnormal (K₂.subgroupOf K) (Y.subgroupOf K) :=
    A3.subnormal_comap K.subtype hsub
  have hsub2 : IsSubnormal (imgJ K (pCoreOf 2 K) K₂) (imgJ K (pCoreOf 2 K) Y) :=
    A3.subnormal_map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) hsub1
  have hsub3 : IsSubnormal (imgJ K (pCoreOf 2 K) K₂) (perfectCore (imgJ K (pCoreOf 2 K) Y)) :=
    A3.subnormal_of_le_of_le hsub2 hKL (perfectCore_le _)
  have hN2 : IsPGroup 2 ↥(π.ker.map (perfectCore (imgJ K (pCoreOf 2 K) Y)).subtype) :=
    IsPGroup.map hker _
  have hNL : π.ker.map (perfectCore (imgJ K (pCoreOf 2 K) Y)).subtype ≤
      perfectCore (imgJ K (pCoreOf 2 K) Y) := Subgroup.map_subtype_le _
  rcases subnormal_image_bot_or_top hsub3 hQ π hπ with h0 | h1
  · exfalso
    apply hns
    have hKN : imgJ K (pCoreOf 2 K) K₂ ≤
        π.ker.map (perfectCore (imgJ K (pCoreOf 2 K) Y)).subtype := by
      intro x hx
      have hxL : x ∈ perfectCore (imgJ K (pCoreOf 2 K) Y) := hKL hx
      have : (⟨x, hxL⟩ : ↥(perfectCore (imgJ K (pCoreOf 2 K) Y))) ∈ π.ker := by
        have h2 : (⟨x, hxL⟩ : ↥(perfectCore (imgJ K (pCoreOf 2 K) Y))) ∈
            (imgJ K (pCoreOf 2 K) K₂).subgroupOf (perfectCore (imgJ K (pCoreOf 2 K) Y)) := hx
        have h3 := Subgroup.mem_map_of_mem π h2
        rw [h0] at h3
        exact h3
      exact ⟨⟨x, hxL⟩, this, rfl⟩
    have hKh2 : IsPGroup 2 ↥(imgJ K (pCoreOf 2 K) K₂) := hN2.to_le hKN
    have hKhs : Group.IsSolvable ↥(imgJ K (pCoreOf 2 K) K₂) := by
      have := hKh2.isNilpotent
      infer_instance
    exact isSolvable_of_imgJ hK₂K hKhs
  · have hLKN : perfectCore (imgJ K (pCoreOf 2 K) Y) ≤ imgJ K (pCoreOf 2 K) K₂ ⊔
        π.ker.map (perfectCore (imgJ K (pCoreOf 2 K) Y)).subtype := by
      intro x hx
      have h2 : π ⟨x, hx⟩ ∈ (( imgJ K (pCoreOf 2 K) K₂).subgroupOf
          (perfectCore (imgJ K (pCoreOf 2 K) Y))).map π := by rw [h1]; trivial
      obtain ⟨y, hy, hyx⟩ := h2
      have hy' : (y : KBar K) ∈ imgJ K (pCoreOf 2 K) K₂ := hy
      have hker' : (y⁻¹ * ⟨x, hx⟩ : ↥(perfectCore (imgJ K (pCoreOf 2 K) Y))) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hmem : ((y⁻¹ * ⟨x, hx⟩ : ↥(perfectCore (imgJ K (pCoreOf 2 K) Y))) : KBar K) ∈
          π.ker.map (perfectCore (imgJ K (pCoreOf 2 K) Y)).subtype := ⟨_, hker', rfl⟩
      have : x = (y : KBar K) * ((y⁻¹ * ⟨x, hx⟩ :
          ↥(perfectCore (imgJ K (pCoreOf 2 K) Y))) : KBar K) := by
        simp
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hy') (Subgroup.mem_sup_right hmem)
    exact eq_of_subnormal_of_le_sup hNL (perfectCore_perfect _) hN2 hsub3 hLKN

theorem exists_kbar_equiv {K Y K₂ : Subgroup G} (hK₂Y : K₂ ≤ Y) (hYK : Y ≤ K)
    (heq : imgJ K (pCoreOf 2 K) K₂ = perfectCore (imgJ K (pCoreOf 2 K) Y))
    {Q : Type} [Group Q] (π : ↥(perfectCore (imgJ K (pCoreOf 2 K) Y)) →* Q)
    (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker) (hQ : IsSimpleGroup Q)
    (hQnab : ∃ a b : Q, a * b ≠ b * a) : Nonempty (KBar K₂ ≃* Q) := by
  have hK₂K : K₂ ≤ K := hK₂Y.trans hYK
  have : Finite Q := Finite.of_surjective π hπ
  set f := (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).comp (Subgroup.inclusion hK₂K)
    with hf
  have hrange : f.range = perfectCore (imgJ K (pCoreOf 2 K) Y) := by
    rw [hf, range_toKBar hK₂K, heq]
  let ψ : ↥K₂ →* ↥(perfectCore (imgJ K (pCoreOf 2 K) Y)) :=
    f.codRestrict _ (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have : (y : KBar K) ∈ f.range := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  have hψker : IsPGroup 2 ψ.ker := by
    have : ψ.ker = f.ker := by
      ext x
      simp [ψ, MonoidHom.mem_ker]
    rw [this]
    exact isPGroup_ker_toKBar hK₂K
  let g : ↥K₂ →* Q := π.comp ψ
  have hg : Function.Surjective g := hπ.comp hψsurj
  have hgker : IsPGroup 2 g.ker := by
    have : g.ker = π.ker.comap ψ := by
      rw [← MonoidHom.comap_ker]
    rw [this]
    exact hker.comap_of_ker_isPGroup ψ hψker
  exact ⟨(kbarEquivQuot K₂).trans (modO2Equiv' hQnab g hg hgker)⟩

end Ident

end CFSG.Quasithin.GoldS146R
