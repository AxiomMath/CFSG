module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3ParaA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Quasithin.H13.A6.A6L76Of CFSG.Quasithin.H13.A6.A6L76Z CFSG.Quasithin.H13.A6.A6L76N3

noncomputable section

private theorem s1611e3_mem_centSub_zpowers {W : Type} [CommGroup W] (w : W) (g : MulAut W) :
    g ∈ centSub (Subgroup.zpowers w) ↔ g w = w := by
  rw [mem_centSub]
  constructor
  · intro h; exact h w (Subgroup.mem_zpowers w)
  · intro h
    have hle : Subgroup.zpowers w ≤ fixV (Subgroup.zpowers g) :=
      Subgroup.zpowers_le.mpr (mem_fixV_zpowers_iff_apply.mpr h)
    intro u hu
    have hu' : u ∈ fixV (Subgroup.zpowers g) := hle hu
    rw [mem_fixV] at hu'
    exact hu' g (Subgroup.mem_zpowers g)

private theorem s1611e3_pi_injective {K : Type} [Field K]
    {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {I : Subgroup W}
    {π : ↥(StatedSL 3 K) →* ↥L}
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia L I ⊥ π) :
    Function.Injective π := by
  obtain ⟨hπsurj, hπI, β, hβsurj, hβker, hβeqv⟩ := natRealizes_clean (F := K) hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : W) ∈ (⊥ : Subgroup W) := (hβker u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro γ hγ
  have hπγ : π γ = 1 := MonoidHom.mem_ker.mp hγ
  apply natHom_injective (F := K)
  refine MulEquiv.ext fun m => ?_
  obtain ⟨u, rfl⟩ := hβsurj m
  have hmem : ((π γ : ↥L) : MulAut W) (u : W) ∈ I := hπI (π γ) (u : W) u.2
  have he := hβeqv γ u hmem
  have hap : ((π γ : ↥L) : MulAut W) (u : W) = (u : W) := by
    rw [hπγ, Subgroup.coe_one, MulAut.one_apply]
  have hEq : (⟨((π γ : ↥L) : MulAut W) (u : W), hmem⟩ : ↥I) = u := Subtype.ext hap
  have he' : β u = natHom γ (β u) := (congrArg β hEq).symm.trans he
  rw [map_one, MulAut.one_apply]
  exact he'.symm

theorem s1611e3_transport_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {I : Subgroup W}
    {π : ↥(StatedSL 3 K) →* ↥L}
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia L I ⊥ π)
    {T₁ : Subgroup (MulAut W)} (hT₁L : T₁ ≤ L) (hT₁ : IsSylowIn 2 T₁ L) :
    Nat.card ↥(I ⊓ fixV T₁) = 2 := by
  obtain ⟨hπsurj, hπI, β, hβsurj, hβker, hβeqv⟩ := natRealizes_clean (F := K) hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : W) ∈ (⊥ : Subgroup W) := (hβker u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  let βe : ↥I ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  have hπinj : Function.Injective π := s1611e3_pi_injective hπ
  let P : Subgroup ↥(StatedSL 3 K) := (T₁.subgroupOf L).comap π
  have hmemP : ∀ γ : ↥(StatedSL 3 K), γ ∈ P ↔ ((π γ : ↥L) : MulAut W) ∈ T₁ := by
    intro γ
    change γ ∈ (T₁.subgroupOf L).comap π ↔ ((π γ : ↥L) : MulAut W) ∈ T₁
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 (T₁.subgroupOf L) := hT₁.2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe hT₁L).symm
    exact h1.comap_of_injective π hπinj
  have hPodd : ¬ 2 ∣ P.index := by
    have h1 : P.index = (T₁.subgroupOf L).index := Subgroup.index_comap_of_surjective _ hπsurj
    rw [h1]
    have h2 : (T₁.subgroupOf L).index = T₁.relIndex L := rfl
    rw [h2]
    exact hT₁.2.2
  have hsub_eq : (I ⊓ fixV T₁).subgroupOf I =
      (s1611e3_fixSub P).comap βe.toMonoidHom := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro hu
      show β u ∈ s1611e3_fixSub P
      intro γ hγ
      have hπγ : ((π γ : ↥L) : MulAut W) ∈ T₁ := (hmemP γ).1 hγ
      have hu2 : ((π γ : ↥L) : MulAut W) (u : W) = (u : W) := hu.2 _ hπγ
      have hmem : ((π γ : ↥L) : MulAut W) (u : W) ∈ I := hπI (π γ) (u : W) u.2
      have he := hβeqv γ u hmem
      have hEq : (⟨((π γ : ↥L) : MulAut W) (u : W), hmem⟩ : ↥I) = u := Subtype.ext hu2
      have he' : β u = natHom γ (β u) := (congrArg β hEq).symm.trans he
      exact he'.symm
    · intro hu
      refine ⟨u.2, ?_⟩
      intro t ht
      obtain ⟨γ, hγ⟩ := hπsurj ⟨t, hT₁L ht⟩
      have hγP : γ ∈ P := by
        rw [hmemP]
        show ((π γ : ↥L) : MulAut W) ∈ T₁
        rw [hγ]
        exact ht
      have hfix := hu γ hγP
      have hmem : ((π γ : ↥L) : MulAut W) (u : W) ∈ I := hπI (π γ) (u : W) u.2
      have he := hβeqv γ u hmem
      have h1 : β ⟨((π γ : ↥L) : MulAut W) (u : W), hmem⟩ = β u := he.trans hfix
      have hval := congrArg Subtype.val (βe.injective h1)
      simpa [hγ] using hval
  have hcard_fix_mid : Nat.card ↥(I ⊓ fixV T₁) = Nat.card ↥(s1611e3_fixSub P) := by
    rw [← Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : I ⊓ fixV T₁ ≤ I)).toEquiv]
    rw [hsub_eq]
    refine Nat.card_congr (Equiv.ofBijective
      (fun γ : ↥((s1611e3_fixSub P).comap βe.toMonoidHom) =>
        (⟨βe γ.1, Subgroup.mem_comap.mp γ.2⟩ : ↥(s1611e3_fixSub P))) ⟨?_, ?_⟩)
    · intro a b hab
      apply Subtype.ext
      exact βe.injective (congrArg Subtype.val hab)
    · intro y
      refine ⟨⟨βe.symm y.1, ?_⟩, ?_⟩
      · rw [Subgroup.mem_comap]
        simpa using y.2
      · apply Subtype.ext
        simp
  rw [hcard_fix_mid, s1611e3_fixSub_card hK hP2 hPodd]

theorem s1611e3_transport_stab {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {I : Subgroup W}
    {π : ↥(StatedSL 3 K) →* ↥L}
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia L I ⊥ π) :
    ∀ w ∈ I, w ≠ 1 → Nat.card ↥(L ⊓ centSub (Subgroup.zpowers w)) = 24 := by
  obtain ⟨hπsurj, hπI, β, hβsurj, hβker, hβeqv⟩ := natRealizes_clean (F := K) hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : W) ∈ (⊥ : Subgroup W) := (hβker u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  let βe : ↥I ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  have hπinj : Function.Injective π := s1611e3_pi_injective hπ
  intro w hw hw1
  let m : Multiplicative (Fin 3 → K) := βe ⟨w, hw⟩
  have hm : m ≠ 1 := by
    intro h
    have hβ1 : β (⟨w, hw⟩ : ↥I) = β 1 := by
      rw [show β (⟨w, hw⟩ : ↥I) = m from rfl, h, map_one]
    have h1 : (⟨w, hw⟩ : ↥I) = 1 := hβinj hβ1
    exact hw1 (by simpa using congrArg Subtype.val h1)
  have hf_mem : ∀ γ : ↥(StatedSL 3 K), γ ∈ s1611e3_stabSL m →
      (π γ : MulAut W) ∈ centSub (Subgroup.zpowers w) := by
    intro γ hγ
    rw [s1611e3_mem_centSub_zpowers]
    have hmem : ((π γ : ↥L) : MulAut W) (w : W) ∈ I := hπI (π γ) (w : W) hw
    have he := hβeqv γ ⟨w, hw⟩ hmem
    have h1 : β ⟨((π γ : ↥L) : MulAut W) (w : W), hmem⟩ = β (⟨w, hw⟩ : ↥I) := by
      rw [he]
      exact hγ
    have hEq : (⟨((π γ : ↥L) : MulAut W) (w : W), hmem⟩ : ↥I) = ⟨w, hw⟩ := βe.injective h1
    exact congrArg Subtype.val hEq
  let f : ↥(s1611e3_stabSL m) → ↥(L ⊓ centSub (Subgroup.zpowers w)) := fun γ =>
    ⟨(π γ.1 : MulAut W), ⟨(π γ.1).2, hf_mem γ.1 γ.2⟩⟩
  have hcard : Nat.card ↥(L ⊓ centSub (Subgroup.zpowers w)) = Nat.card ↥(s1611e3_stabSL m) := by
    refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
    · intro γ δ hγδ
      apply Subtype.ext
      apply hπinj
      apply Subtype.ext
      exact congrArg (fun x : ↥(L ⊓ centSub (Subgroup.zpowers w)) => (x.1 : MulAut W)) hγδ
    · intro l
      obtain ⟨γ, hγ⟩ := hπsurj ⟨(l.1 : MulAut W), l.2.1⟩
      have hlw : (l.1 : MulAut W) w = w :=
        (s1611e3_mem_centSub_zpowers w l.1).mp l.2.2
      have hγm : γ ∈ s1611e3_stabSL m := by
        have hmem : ((π γ : ↥L) : MulAut W) (w : W) ∈ I := hπI (π γ) (w : W) hw
        have he := hβeqv γ ⟨w, hw⟩ hmem
        have hπγw : ((π γ : ↥L) : MulAut W) (w : W) = (w : W) := by
          rw [hγ]
          exact hlw
        have h1 : β (⟨w, hw⟩ : ↥I) = natHom γ (β ⟨w, hw⟩) :=
          (congrArg β (Subtype.ext hπγw)).symm.trans he
        show natHom γ m = m
        rw [show m = β ⟨w, hw⟩ from rfl]
        exact h1.symm
      refine ⟨⟨γ, hγm⟩, ?_⟩
      apply Subtype.ext
      change (π γ : MulAut W) = (l.1 : MulAut W)
      rw [hγ]
  rw [hcard, s1611e3_stabSL_card hK hm]

end
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
