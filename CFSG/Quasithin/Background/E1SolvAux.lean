module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.E1Sec7

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

section WeakClosure

variable {G : Type*} [Group G]

theorem weakClosure_le {X : Subgroup G} {Ω : Set (Subgroup G)} : weakClosure X Ω ≤ X :=
  iSup₂_le fun _ _ => iSup_le fun h => h

theorem le_weakClosure {X A : Subgroup G} {Ω : Set (Subgroup G)} (hA : A ∈ Ω) (hAX : A ≤ X) :
    A ≤ weakClosure X Ω :=
  le_iSup₂_of_le A hA (le_iSup_of_le hAX le_rfl)

theorem le_eGen {i : ℕ} {H T A K : Subgroup G} {Ω : Set (Subgroup G)} (hA : A ∈ Ω) (hAT : A ≤ T)
    (hK : IsE i H T A K) : K ≤ eGen i H T Ω :=
  le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hK le_rfl))

theorem mem_normalizer_weakClosure [Finite G] {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsInvColl ⊤ Ω) {x : G} (hx : ∀ w ∈ weakClosure T Ω, x * w * x⁻¹ ∈ T) :
    x ∈ Subgroup.normalizer (weakClosure T Ω : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : weakClosure T Ω ≤ (weakClosure T Ω).comap (MulAut.conj x).toMonoidHom := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    intro a ha
    rw [Subgroup.mem_comap]
    have h1 : conjSub x A ∈ Ω := hΩ.conj A hA x (Subgroup.mem_top x)
    have h2 : conjSub x A ≤ T := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h3 : x * (x⁻¹ * y * x) * x⁻¹ ∈ T := hx _ (le_weakClosure hA hAT hy)
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [e] at h3
    exact le_weakClosure h1 h2 (mem_conjSub_of_mem ha)
  intro w hw
  exact hle hw

theorem le_normalizer_weakClosure [Finite G] {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsInvColl ⊤ Ω) : T ≤ Subgroup.normalizer (weakClosure T Ω : Set G) := by
  intro t ht
  apply mem_normalizer_weakClosure hΩ
  intro w hw
  exact T.mul_mem (T.mul_mem ht (weakClosure_le hw)) (T.inv_mem ht)

end WeakClosure

section Quotient

variable {Q : Type*} [Group Q]

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup Q} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem isInvColl_map_of_surjective {Q' : Type*} [Group Q'] (f : Q →* Q')
    (hf : Function.Surjective f) {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω) :
    IsInvColl ⊤ (Subgroup.map f '' Ω) := by
  refine ⟨fun _ _ => le_top, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact isElemAbelian_map' f (hΩ.isElemAbelian A hA)
  · rintro _ ⟨A, hA, rfl⟩ h' _
    obtain ⟨g, rfl⟩ := hf h'
    refine ⟨conjSub g A, hΩ.conj A hA g (Subgroup.mem_top g), ?_⟩
    show (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]

variable [Finite Q]

theorem exists_mem_conj_le_of_map_le {N T A₀ : Subgroup Q} [N.Normal] (hT : IsSylowIn 2 T ⊤)
    (hA₀ : IsPGroup 2 A₀)
    (h : A₀.map (QuotientGroup.mk' N) ≤ T.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, ∀ a ∈ A₀, n * a * n⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA₀le : A₀ ≤ T ⊔ N := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := h (Subgroup.mem_map_of_mem _ ha)
    have h1 : t⁻¹ * a ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hta]
      simp
    have e : a = t * (t⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem_sup ht h1
  obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 hA₀le hA₀
  have hT' : IsSylowTwoOf T (T ⊔ N) := B6.isSylowTwoOf_mono hT le_sup_left le_top
  obtain ⟨g, hg, hgS⟩ := B6.isSylowTwoOf_exists_conj hT' hS
  have hTN : T ≤ Subgroup.normalizer (N : Set Q) := fun t _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top t
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N T hTN] at hg
  obtain ⟨n, hn, t, ht, rfl⟩ := hg
  refine ⟨n⁻¹, N.inv_mem hn, fun a ha => ?_⟩
  have h1 : a ∈ B6.conjSub (n * t) T := by
    rw [← hgS]
    exact hAS ha
  rw [B6.mem_conjSub] at h1
  have h2 : n⁻¹ * a * n⁻¹⁻¹ = t * ((n * t)⁻¹ * a * (n * t)) * t⁻¹ := by group
  rw [h2]
  exact T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht)

theorem weakClosure_map_quotient {N T : Subgroup Q} [N.Normal] (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω) :
    weakClosure (T.map (QuotientGroup.mk' N)) (Subgroup.map (QuotientGroup.mk' N) '' Ω) =
      (weakClosure T Ω).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N with hπ
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => ?_
    obtain ⟨A₀, hA₀, rfl⟩ := hA'
    obtain ⟨n, hn, hnA⟩ := exists_mem_conj_le_of_map_le hT
      (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A₀ hA₀)) hA'T
    have hconj : conjSub n A₀ ∈ Ω := hΩ.conj A₀ hA₀ n (Subgroup.mem_top n)
    have hle : conjSub n A₀ ≤ T := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      have := hnA _ hy
      rwa [e] at this
    refine le_trans ?_ (Subgroup.map_mono (le_weakClosure hconj hle))
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨n * a * n⁻¹, mem_conjSub_of_mem ha, ?_⟩
    have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    simp [hπn]
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_weakClosure ⟨A, hA, rfl⟩ (Subgroup.map_mono hAT)

theorem exists_mem_normalizer_of_mem_normalizer_map {N T : Subgroup Q} [N.Normal]
    (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω) {g : Q}
    (hg : QuotientGroup.mk' N g ∈
      Subgroup.normalizer ((weakClosure T Ω).map (QuotientGroup.mk' N) : Set (Q ⧸ N))) :
    ∃ g' ∈ Subgroup.normalizer (weakClosure T Ω : Set Q),
      QuotientGroup.mk' N g' = QuotientGroup.mk' N g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set W := weakClosure T Ω with hW
  have hWT : W ≤ T := weakClosure_le
  set V : Subgroup Q := W ⊔ N with hV
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hVcomap : V = (W.map π).comap π := by
    rw [Subgroup.comap_map_eq, hker]
  have hWV : W ≤ V := le_sup_left
  have hNV : N ≤ V := le_sup_right
  have hSyl : IsSylowIn 2 (T ⊓ V) V := by
    have hidx : ¬ 2 ∣ T.index := by
      have := hT.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this
    let C : Sylow 2 Q := hT.isPGroup.toSylow hidx
    have hC : (C : Subgroup Q) = T := rfl
    have hVmap : V.map π = W.map π := by
      rw [hV, Subgroup.map_sup, (Subgroup.map_eq_bot_iff N).mpr hker.ge, sup_bot_eq]
    have hWW : IsSylowIn 2 (W.map π) (W.map π) :=
      ⟨le_rfl, (hT.isPGroup.to_le hWT).map π, by
        rw [Subgroup.relIndex_self]
        norm_num⟩
    have := isSylowIn_inf_of_quotient N hNV C (by
      rw [hC, hVmap, inf_eq_right.mpr (Subgroup.map_mono hWT)]
      exact hWW)
    rwa [hC] at this
  have hgV : g ∈ Subgroup.normalizer (V : Set Q) := by
    apply mem_normalizer_of_conj_mem
    intro v hv
    rw [hVcomap] at hv ⊢
    rw [Subgroup.mem_comap] at hv ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg (π v)).mp hv
  have hS : IsSylowTwoOf (T ⊓ V) V := hSyl
  have hS' : IsSylowTwoOf (B6.conjSub g (T ⊓ V)) V := by
    have := B6.isSylowTwoOf_conjSub hS g
    rwa [B6.conjSub_eq_self hgV] at this
  obtain ⟨v, hv, hvS⟩ := B6.isSylowTwoOf_exists_conj hS hS'
  set g' := v⁻¹ * g with hg'
  have hg'S : ∀ s ∈ T ⊓ V, g' * s * g'⁻¹ ∈ T ⊓ V := by
    intro s hs
    have h1 : g * s * g⁻¹ ∈ B6.conjSub g (T ⊓ V) := by
      have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      rw [B6.mem_conjSub, e]
      exact hs
    rw [hvS, B6.mem_conjSub] at h1
    have e : g' * s * g'⁻¹ = v⁻¹ * (g * s * g⁻¹) * v := by rw [hg']; group
    rw [e]
    exact h1
  have hg'N : g' ∈ Subgroup.normalizer (W : Set Q) := by
    apply mem_normalizer_weakClosure hΩ
    intro w hw
    exact (hg'S w ⟨hWT hw, hWV hw⟩).1
  have hπv : π v ∈ W.map π := by
    have : v ∈ (W.map π).comap π := by
      rw [← hVcomap]
      exact hv
    exact this
  obtain ⟨w, hw, hwv⟩ := hπv
  refine ⟨w * g', Subgroup.mul_mem _ (Subgroup.le_normalizer hw) hg'N, ?_⟩
  rw [map_mul, hwv, ← map_mul]
  congr 1
  rw [hg']
  group

theorem le_twoResidual_sup_of_isSylowIn {K S : Subgroup Q} (hS : IsSylowIn 2 S K) :
    K ≤ twoResidual K ⊔ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hN : ((twoResidual K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le K)).mpr
      (le_normalizer_twoResidual K)
  obtain ⟨s, hs, n, hn, rfl⟩ := exists_mul_eq_of_pow_mem hN
    (fun y hy => twoResidual_isTwoQuotient K y hy) hS x hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left hn)

end Quotient

section Commutator

variable {Q : Type*} [Group Q]

theorem commutator_weakClosure_le {N N₁ T : Subgroup Q} {Ω : Set (Subgroup Q)}
    (hN₁ : T ≤ Subgroup.normalizer (N₁ : Set Q))
    (h : ∀ A ∈ Ω, A ≤ T → ⁅N, A⁆ ≤ N₁) : ⁅N, weakClosure T Ω⁆ ≤ N₁ := by
  let C : Subgroup Q :=
    { carrier := {g | g ∈ Subgroup.normalizer (N₁ : Set Q) ∧ ∀ n ∈ N, ⁅n, g⁆ ∈ N₁}
      one_mem' := ⟨Subgroup.one_mem _, fun n _ => by simp [N₁.one_mem]⟩
      mul_mem' := by
        rintro g k ⟨hgN, hg⟩ ⟨hkN, hk⟩
        refine ⟨Subgroup.mul_mem _ hgN hkN, fun n hn => ?_⟩
        have e : ⁅n, g * k⁆ = ⁅n, g⁆ * (g * ⁅n, k⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine N₁.mul_mem (hg n hn) ?_
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp (hk n hn)
      inv_mem' := by
        rintro g ⟨hgN, hg⟩
        refine ⟨Subgroup.inv_mem _ hgN, fun n hn => ?_⟩
        have e : ⁅n, g⁻¹⁆ = g⁻¹ * (⁅n, g⁆)⁻¹ * g := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp
          (N₁.inv_mem (hg n hn))
        simpa using this }
  have hWC : weakClosure T Ω ≤ C := by
    refine iSup₂_le fun A hA => iSup_le fun hAT a ha => ?_
    exact ⟨hN₁ (hAT ha), fun n hn =>
      h A hA hAT (Subgroup.commutator_mem_commutator hn ha)⟩
  exact Subgroup.commutator_le.mpr fun n hn g hg => (hWC hg).2 n hn

end Commutator

end E1

end CFSG.Quasithin
