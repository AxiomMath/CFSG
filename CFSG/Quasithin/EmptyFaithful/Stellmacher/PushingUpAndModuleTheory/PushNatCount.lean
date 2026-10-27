module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushNatPerm
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreZ1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCorePU0
public import CFSG.Quasithin.EmptyFaithful.SzF53MNatL2

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G]

abbrev zZero (X Z : Subgroup G) : Subgroup G :=
  Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)

structure NormData (X S Z : Subgroup G) [((zZero X Z).subgroupOf Z).Normal]
    (Ψ : ↥X →* Perm (Fin 5)) (β : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z) : Prop where
  sec : SecData nat X (zZero X Z) Z Ψ β
  ker : ∀ x : ↥X, Ψ x = 1 → (x : G) ∈ pCoreOf 2 X
  ev : ∀ x : ↥X, (x : G) ∈ pResidualOf 2 X → Perm.sign (Ψ x) = 1
  surj : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → ∃ x : ↥X, Ψ x = τ
  syl : ∀ x : ↥X, (x : G) ∈ S → Ψ x ∈ S5Syl

theorem exists_twist {X S Z : Subgroup G} [((zZero X Z).subgroupOf Z).Normal]
    {θ : ↥X →* Perm (Fin 5)} {β : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z}
    (hsd : SecData nat X (zZero X Z) Z θ β) (hSX : S ≤ X) (hS2 : IsPGroup 2 S)
    (hker : ∀ x : ↥X, θ x = 1 → (x : G) ∈ pCoreOf 2 X)
    (hev : ∀ x : ↥X, (x : G) ∈ pResidualOf 2 X → Perm.sign (θ x) = 1)
    (hsurj : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → ∃ x : ↥X, θ x = τ) :
    ∃ (Ψ : ↥X →* Perm (Fin 5)) (β' : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z),
      NormData X S Z Ψ β' := by
  have hp : IsPGroup 2 ↥(S.subgroupOf X) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  obtain ⟨g, hg⟩ := exists_le_conj_S5Syl (hp.map θ)
  have hkerΨ : ∀ f : ↥X, ((MulAut.conj g⁻¹).toMonoidHom.comp θ) f = 1 ↔ θ f = 1 := fun f =>
    (MulAut.conj g⁻¹).map_eq_one_iff
  have hsgn : ∀ f : ↥X, Perm.sign (((MulAut.conj g⁻¹).toMonoidHom.comp θ) f) = Perm.sign (θ f) :=
    fun f => sign_conj_five _ _
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp θ, β.comp (nat.act (g⁻¹)⁻¹).toMonoidHom,
    ⟨hsd.twist g⁻¹, fun x hx => hker x ((hkerΨ x).mp hx),
      fun x hx => (hsgn x).trans (hev x hx), ?_, ?_⟩⟩
  · intro τ hτ
    obtain ⟨x, hx⟩ := hsurj (g * τ * g⁻¹) (by rw [sign_conj_five]; exact hτ)
    refine ⟨x, ?_⟩
    show g⁻¹ * θ x * g⁻¹⁻¹ = τ
    rw [hx]; group
  · intro x hx
    have h1 : θ x ∈ S5Syl.map (MulAut.conj g).toMonoidHom :=
      hg ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h2 := (mem_map_conj S5Syl g (θ x)).mp h1
    show g⁻¹ * θ x * g⁻¹⁻¹ ∈ S5Syl
    simpa using h2

theorem image_sq_of {X : Subgroup G} (Ψ : ↥X →* Perm (Fin 5)) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) : ∀ b ∈ (A.subgroupOf X).map Ψ, b * b = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_mul]
  have : a * a = 1 := Subtype.ext (by
    have := hA.2 (a : G) (Subgroup.mem_subgroupOf.mp ha)
    simpa [pow_two] using this)
  rw [this, map_one]


namespace NormData

variable {X S Z : Subgroup G} [((zZero X Z).subgroupOf Z).Normal] {Ψ : ↥X →* Perm (Fin 5)}
  {β : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z} (d : NormData X S Z Ψ β)

include d

variable [Finite G]

theorem index_le {A : Subgroup G} (hAX : A ≤ X) :
    (fixW nat ((A.subgroupOf X).map Ψ)).index ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := by
  have hLZ : zZero X Z ≤ Z := inf_le_left
  rw [← d.sec.relIndex_fixSecIn hLZ hAX]
  refine relIndex_le_of_le Z ?_
  rintro z ⟨hz, hzA⟩
  rw [X1512.mem_fixSecIn hLZ]
  refine ⟨hz, fun a ha => ?_⟩
  have h1 : a * z = z * a := Subgroup.mem_centralizer_iff.mp hzA a ha
  have : a * z * a⁻¹ * z⁻¹ = 1 := by rw [h1]; group
  rw [this]
  exact (zZero X Z).one_mem

theorem relIndex_core_le {A : Subgroup G} (hAX : A ≤ X) :
    (A ⊓ pCoreOf 2 X).relIndex A ≤ Nat.card ((A.subgroupOf X).map Ψ) := by
  have hk : Ψ.ker ≤ (pCoreOf 2 X).subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (d.ker x hx)
  have h1 := relIndex_le_of_le (A.subgroupOf X) hk
  rw [Subgroup.relIndex_subgroupOf hAX, Subgroup.relIndex_ker] at h1
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact h1

omit [Finite G] in
theorem image_le_syl {A : Subgroup G} (hAS : A ≤ S) :
    (A.subgroupOf X).map Ψ ≤ S5Syl := by
  rintro _ ⟨a, ha, rfl⟩
  exact d.syl a (hAS (Subgroup.mem_subgroupOf.mp ha))

theorem offender (h : PushHyp X S Z) {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hAQ : ¬ A ≤ pCoreOf 2 X) :
    (A.subgroupOf X).map Ψ = S5T ∧ (A ⊓ pCoreOf 2 X).relIndex A ≤ 4 ∧
      4 ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := by
  have hAX : A ≤ X := hA.1.trans h.le_self
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have haX : a ∈ X := hAX haA
  have hΨa : Ψ ⟨a, haX⟩ ≠ 1 := fun h1 => haQ (d.ker _ h1)
  have hmem : Ψ ⟨a, haX⟩ ∈ (A.subgroupOf X).map Ψ :=
    ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
  have h4 := four_le_index_fixW hmem hΨa
  have hsq := image_sq_of Ψ hA.2.1
  have hBS := d.image_le_syl hA.1
  have hc4 := card_le_four hBS hsq
  have hT1 := offender_count h hA
  have hD := d.index_le hAX
  have hK := d.relIndex_core_le hAX
  have hcard : Nat.card ((A.subgroupOf X).map Ψ) = 4 := by omega
  have hidx : (fixW nat ((A.subgroupOf X).map Ψ)).index ≤ 4 := by omega
  have hle := le_S5T_of_idx hBS hsq hcard hidx
  refine ⟨Subgroup.eq_of_le_of_card_ge hle (by rw [card_S5T, hcard]), by omega, by omega⟩

theorem mem_sup_of_image (h : PushHyp X S Z) {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hAQ : ¬ A ≤ pCoreOf 2 X) {x : ↥X} (hx : Ψ x ∈ S5T) : (x : G) ∈ A ⊔ pCoreOf 2 X := by
  have hAX : A ≤ X := hA.1.trans h.le_self
  have hBA := (d.offender h hA hAQ).1
  rw [← hBA] at hx
  obtain ⟨a, ha, hax⟩ := hx
  have hq : ((x * a⁻¹ : ↥X) : G) ∈ pCoreOf 2 X := by
    refine d.ker _ ?_
    rw [map_mul, map_inv, ← hax, mul_inv_cancel]
  have : (x : G) = ((x * a⁻¹ : ↥X) : G) * (a : G) := by simp
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hq (Subgroup.mem_subgroupOf.mp ha)

theorem thompsonJ_le (h : PushHyp X S Z) {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hAQ : ¬ A ≤ pCoreOf 2 X) : thompsonJ S ≤ A ⊔ pCoreOf 2 X := by
  refine iSup₂_le fun A' hA' => ?_
  by_cases hA'Q : A' ≤ pCoreOf 2 X
  · exact hA'Q.trans le_sup_right
  · have hA'X : A' ≤ X := hA'.1.trans h.le_self
    intro a' ha'
    have hmem : Ψ ⟨a', hA'X ha'⟩ ∈ S5T := by
      rw [← (d.offender h hA' hA'Q).1]
      exact ⟨⟨a', hA'X ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩
    exact d.mem_sup_of_image h hA hAQ hmem

theorem residual_le (h : PushHyp X S Z) {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hAQ : ¬ A ≤ pCoreOf 2 X) : pResidualOf 2 X ⊓ S ≤ A ⊔ pCoreOf 2 X := by
  rintro s ⟨hsL, hsS⟩
  have hsX : s ∈ X := pResidualOf_le_self X hsL
  have hmem : Ψ ⟨s, hsX⟩ ∈ S5T :=
    Subgroup.mem_inf.mpr ⟨d.syl ⟨s, hsX⟩ hsS,
      Equiv.Perm.mem_alternatingGroup.mpr (d.ev ⟨s, hsX⟩ hsL)⟩
  exact d.mem_sup_of_image h hA hAQ hmem

theorem zOne_ge (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    4 ≤ (zOne X S Z).relIndex Z := by
  have hLZ : zZero X Z ≤ Z := inf_le_left
  obtain ⟨j, hjJ, hjQ⟩ := IsConcreteLE.not_le_iff_exists.mp hJ
  have hjX : j ∈ X := h.le_self (thompsonJ_le_self S hjJ)
  have hΨj : Ψ ⟨j, hjX⟩ ≠ 1 := fun h1 => hjQ (d.ker _ h1)
  have hle : zOne X S Z ≤ fixSecIn (Subgroup.zpowers j) (zZero X Z) Z := by
    intro z hz
    obtain ⟨hzZ, hzJ⟩ := (mem_zOne_iff h).mp hz
    rw [X1512.mem_fixSecIn hLZ]
    exact ⟨hzZ, fun a ha => hzJ a (((Subgroup.zpowers_le).mpr hjJ) ha)⟩
  have h1 := relIndex_le_of_le Z hle
  have h2 : (fixSecIn (Subgroup.zpowers j) (zZero X Z) Z).relIndex Z = idx nat (Ψ ⟨j, hjX⟩) :=
    d.sec.secIdx_eq_idx inf_le_left hjX
  have h3 := (transvections _ hΨj).1
  omega

omit [Finite G] in
theorem index_ge : 4 ^ 2 ≤ (zZero X Z).relIndex Z := by
  rw [d.sec.relIndex_eq, card_nat]
  norm_num

theorem generated (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    ∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X := by
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  have hBA₀ := (d.offender h hA₀ hA₀Q).1
  have hJX : thompsonJ S ≤ X := (thompsonJ_le_self S).trans h.le_self
  obtain ⟨x, hx⟩ := d.surj S5c sign_S5c
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidualOf X x.2
  set g : G := (x : G) ^ 2 ^ k with hgdef
  have hgX : g ∈ X := X.pow_mem x.2 _
  have hΨg : Ψ ⟨g, hgX⟩ = S5c ^ 2 ^ k := by
    have : (⟨g, hgX⟩ : ↥X) = x ^ 2 ^ k := rfl
    rw [this, map_pow, hx]
  refine ⟨g, hk, fun l hl => ?_⟩
  have hlX : l ∈ X := pResidualOf_le_self X hl
  have hmem := alt_le_sup_cj (S5c_pow_two_pow k) (Ψ ⟨l, hlX⟩) (d.ev ⟨l, hlX⟩ hl)
  rw [← hΨg] at hmem
  set I₂ := thompsonJ S ⊔ cj g (thompsonJ S) with hI₂
  have hI₂X : I₂ ≤ X := sup_le hJX (cj_le_of_mem hgX hJX)
  set K : Subgroup (Perm (Fin 5)) := (I₂.subgroupOf X).map Ψ with hK
  have hKT : S5T ≤ K := by
    intro τ hτ
    rw [← hBA₀] at hτ
    obtain ⟨a, ha, rfl⟩ := hτ
    exact ⟨a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left
      (le_thompsonJ_of_isMax hA₀ (Subgroup.mem_subgroupOf.mp ha))), rfl⟩
  have hKc : cj (Ψ ⟨g, hgX⟩) S5T ≤ K := by
    intro τ hτ
    rw [mem_cj, ← hBA₀] at hτ
    obtain ⟨a, ha, hax⟩ := hτ
    refine ⟨⟨g, hgX⟩ * a * ⟨g, hgX⟩⁻¹, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right ?_), ?_⟩
    · rw [mem_cj]
      have := le_thompsonJ_of_isMax hA₀ (Subgroup.mem_subgroupOf.mp ha)
      show g⁻¹ * (g * (a : G) * g⁻¹) * g ∈ thompsonJ S
      simpa [mul_assoc] using this
    · rw [map_mul, map_mul, map_inv, hax]; group
  obtain ⟨y, hy, hyl⟩ := (sup_le hKT hKc) hmem
  have hq : ((⟨l, hlX⟩ * y⁻¹ : ↥X) : G) ∈ pCoreOf 2 X := by
    refine d.ker _ ?_
    rw [map_mul, map_inv, hyl, mul_inv_cancel]
  have : l = ((⟨l, hlX⟩ * y⁻¹ : ↥X) : G) * (y : G) := by simp
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hq (Subgroup.mem_subgroupOf.mp hy)

theorem natCounts (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    NatCounts X S Z 4 :=
  natCounts_of_zOne h (fun _ hA hAQ => (d.offender h hA hAQ).2.1)
    (fun _ hA hAQ => (d.offender h hA hAQ).2.2) (fun _ hA hAQ => d.thompsonJ_le h hA hAQ)
    (fun _ hA hAQ => d.residual_le h hA hAQ) (d.zOne_ge h hJ) (d.generated h hJ) d.index_ge

end NormData

theorem natCounts_of_secData [Finite G] {X S Z : Subgroup G} (h : PushHyp X S Z)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) [((zZero X Z).subgroupOf Z).Normal]
    {θ : ↥X →* Perm (Fin 5)} {β : nat.W →* ↥Z ⧸ (zZero X Z).subgroupOf Z}
    (hsd : SecData nat X (zZero X Z) Z θ β)
    (hker : ∀ x : ↥X, θ x = 1 → (x : G) ∈ pCoreOf 2 X)
    (hev : ∀ x : ↥X, (x : G) ∈ pResidualOf 2 X → Perm.sign (θ x) = 1)
    (hsurj : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → ∃ x : ↥X, θ x = τ) :
    NatCounts X S Z 4 := by
  obtain ⟨Ψ, β', d⟩ := exists_twist hsd h.le_self h.sylow.2.1 hker hev hsurj
  exact d.natCounts h hJ

end CFSG.Quasithin.F53Push
