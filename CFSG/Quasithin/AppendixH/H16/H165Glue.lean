module

public import CFSG.Quasithin.AppendixH.H16.ConjNat
public import CFSG.Quasithin.AppendixH.H16.SextetO23

public section

open scoped Pointwise

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24

variable {V : Type*} [CommGroup V] {Γ : Subgroup S24}

theorem rImg_conjSubg (ρ : ↥Γ →* MulAut V) (τ : ↥Γ) (A : Subgroup S24) :
    rImg ρ (conjSubg (τ : S24) A) = (rImg ρ A).map (MulAut.conj (ρ τ)).toMonoidHom := by
  have h1 : (conjSubg (τ : S24) A).subgroupOf Γ =
      (A.subgroupOf Γ).map (MulAut.conj τ).toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_conjSubg_iff, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨τ⁻¹ * x * τ, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
      · simpa using hx
      · change τ * (τ⁻¹ * x * τ) * τ⁻¹ = x
        group
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : S24) ∈ A := Subgroup.mem_subgroupOf.1 hy
      have e : (τ : S24)⁻¹ * ((τ : S24) * (y : S24) * (τ : S24)⁻¹) * (τ : S24) = (y : S24) := by
        group
      change (τ : S24)⁻¹ * ((τ : S24) * (y : S24) * (τ : S24)⁻¹) * (τ : S24) ∈ A
      rw [e]
      exact hy'
  have h2 : ρ.comp (MulAut.conj τ).toMonoidHom = (MulAut.conj (ρ τ)).toMonoidHom.comp ρ := by
    ext y
    simp [MulAut.conj_apply]
  unfold rImg
  rw [h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem eq_of_rImg_eq {ρ : ↥Γ →* MulAut V} (hρ : Function.Injective ρ) {A B : Subgroup S24}
    (hA : A ≤ Γ) (hB : B ≤ Γ) (h : rImg ρ A = rImg ρ B) : A = B := by
  have h1 : A.subgroupOf Γ = B.subgroupOf Γ := by
    have := congrArg (Subgroup.comap ρ) h
    unfold rImg at this
    rwa [Subgroup.comap_map_eq_self_of_injective hρ,
      Subgroup.comap_map_eq_self_of_injective hρ] at this
  have h2 := Subgroup.subgroupOf_inj.1 h1
  rwa [inf_eq_left.2 hA, inf_eq_left.2 hB] at h2

theorem conjSubg_le_of_mem {τ : S24} (hτ : τ ∈ Γ) {A : Subgroup S24} (hA : A ≤ Γ) :
    conjSubg τ A ≤ Γ := by
  intro x hx
  rw [mem_conjSubg_iff] at hx
  have h := Γ.mul_mem (Γ.mul_mem hτ (hA hx)) (Γ.inv_mem hτ)
  have e : τ * (τ⁻¹ * x * τ) * τ⁻¹ = x := by group
  rwa [e] at h

theorem KY_le {α : Type*} [MulAction S24 α] (Γ : Subgroup S24) (Y : α) : KY Γ Y ≤ Γ :=
  (pCoreOf_le_subgroup 2 _).trans inf_le_left

theorem h165_card_conjSubg {X : Type*} [Group X] (g : X) (A : Subgroup X) :
    Nat.card (conjSubg g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isElemAbelian_conjSubg {X : Type*} [Group X] {A : Subgroup X} (h : IsElemAbelian 2 A)
    (g : X) : IsElemAbelian 2 (conjSubg g A) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    show (x : X) * y = y * x
    rw [← hax, ← hby]
    have hc := h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    have hc' : a * b = b * a := congrArg Subtype.val hc
    change g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hc']
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, h.2 a ha, map_one]

theorem KY_sextet_facts
    {S : Finset (Finset (Fin 24))}
    (hS : IsSextet S) :
    Nat.card (KY M24g S) = 2 ^ 6 ∧ IsElemAbelian 2 (KY M24g S) := by
  obtain ⟨τ, hτ, rfl⟩ := exists_smul_stdSextet hS
  rw [KY_smul_of_mem hτ, KY, MY_stdSextet_eq, pCoreOf_two_sxGen]
  have hKS : IsElemAbelian 2 sxKS := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      exact ((sxKS_elem _ x.2).2 _ y.2)
    · have := (sxKS_elem x hx).1
      rw [pow_two]
      exact this
  exact ⟨(h165_card_conjSubg τ sxKS).trans (card_sxKS.trans (by norm_num)),
    isElemAbelian_conjSubg hKS τ⟩

theorem isElemAbelian_of_rImg {ρ : ↥Γ →* MulAut V} (hρ : Function.Injective ρ) {A : Subgroup S24}
    (hA : A ≤ Γ) (h : IsElemAbelian2 (rImg ρ A)) : IsElemAbelian 2 A := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hx' : ρ ⟨x, hA x.2⟩ ∈ rImg ρ A := Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    have hy' : ρ ⟨y, hA y.2⟩ ∈ rImg ρ A := Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 y.2, rfl⟩
    have h1 := hc _ hx' _ hy'
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (hρ h1)
    exact h2
  · have hx' : ρ ⟨x, hA hx⟩ ∈ rImg ρ A := Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have h1 := hs _ hx'
    rw [← map_pow] at h1
    have h2 : (⟨x, hA hx⟩ : ↥Γ) ^ 2 = 1 := hρ (by rw [h1, map_one])
    have h3 := congrArg Subtype.val h2
    simpa using h3

theorem exists_conj_le_of_isSylowIn_glue {T A : Subgroup S24}
    (hT : IsSylowIn 2 T Γ) (hAΓ : A ≤ Γ) (hA : IsPGroup 2 A) :
    ∃ g ∈ Γ, conjSubg g A ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Γ := inferInstance
  have hPX : IsPGroup 2 (A.subgroupOf Γ) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAΓ).symm
  obtain ⟨Q, hQ⟩ := hPX.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥Γ) Q hT.toSylow
  refine ⟨(c : S24), c.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : (⟨x, hAΓ hx⟩ : ↥Γ) ∈ (Q : Subgroup ↥Γ) := hQ (Subgroup.mem_subgroupOf.mpr hx)
  have h2 : c * ⟨x, hAΓ hx⟩ * c⁻¹ ∈ ((c • Q : Sylow 2 ↥Γ) : Subgroup ↥Γ) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxQ, by simp [MulAut.conj_apply]⟩
  rw [hc, IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at h2
  simpa [MulAut.conj_apply] using h2

end CFSG.ASVolI.H16
