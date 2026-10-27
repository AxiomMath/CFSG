module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

theorem s16c167_frame_mem_centerF {A : Type*} [Group A] {F : Subgroup A} {z : A} :
    z ∈ (Subgroup.center ↥F).map F.subtype ↔ z ∈ F ∧ ∀ f ∈ F, z * f = f * z := by
  constructor
  · intro hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨x.2, fun f hf => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨f, hf⟩).symm
  · rintro ⟨hzF, hcomm⟩
    refine Subgroup.mem_map.mpr ⟨⟨z, hzF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2).symm

theorem s16c167_frame_centerF_conj {A : Type*} [Group A] {X F : Subgroup A}
    (hFn : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F) :
    ∀ x ∈ X, ((Subgroup.center ↥F).map F.subtype).map (MulAut.conj x).toMonoidHom =
      (Subgroup.center ↥F).map F.subtype := by
  have hsub : ∀ x ∈ X, ∀ z ∈ (Subgroup.center ↥F).map F.subtype,
      x * z * x⁻¹ ∈ (Subgroup.center ↥F).map F.subtype := by
    intro x hx z hz
    rw [s16c167_frame_mem_centerF] at hz ⊢
    obtain ⟨hzF, hzc⟩ := hz
    refine ⟨hFn x hx z hzF, fun f hf => ?_⟩
    have hxf : x⁻¹ * f * x ∈ F := by
      have h := hFn x⁻¹ (X.inv_mem hx) f hf
      simpa using h
    calc
      (x * z * x⁻¹) * f = x * (z * (x⁻¹ * f * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * f * x) * z) * x⁻¹ := by rw [hzc (x⁻¹ * f * x) hxf]
      _ = f * (x * z * x⁻¹) := by group
  intro x hx
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hsub x hx w hw
  · intro z hz
    rw [Subgroup.mem_map]
    refine ⟨x⁻¹ * z * x, ?_, ?_⟩
    · have h := hsub x⁻¹ (X.inv_mem hx) z hz
      simpa using h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem s16c167_frame_centerF_card {A : Type*} [Group A] {F : Subgroup A} {Z S : Type*}
    [CommGroup Z] [Group S] (hS : ∀ s : S, (∀ t : S, s * t = t * s) → s = 1)
    (e : ↥F ≃* Z × S × S) :
    Nat.card ↥((Subgroup.center ↥F).map F.subtype) = Nat.card Z := by
  have hcenterS : Subgroup.center S = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    exact hS s fun t => (Subgroup.mem_center_iff.mp hs t).symm
  rw [Subgroup.card_map_of_injective F.subtype_injective]
  calc
    Nat.card ↥(Subgroup.center ↥F) = Nat.card ↥(Subgroup.center (Z × S × S)) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    _ = Nat.card ↥((Subgroup.center Z).prod
          ((Subgroup.center S).prod (Subgroup.center S))) := by
      rw [Subgroup.center_prod, Subgroup.center_prod]
    _ = Nat.card ↥((⊤ : Subgroup Z).prod
          ((⊥ : Subgroup S).prod (⊥ : Subgroup S))) := by
      rw [CommGroup.center_eq_top, hcenterS]
    _ = Nat.card Z := by
      rw [Nat.card_congr
        (Subgroup.prodEquiv (⊤ : Subgroup Z)
          ((⊥ : Subgroup S).prod (⊥ : Subgroup S))).toEquiv]
      have h1 : Nat.card ↥((⊥ : Subgroup S).prod (⊥ : Subgroup S)) = 1 := by
        rw [Nat.card_congr
            (Subgroup.prodEquiv (⊥ : Subgroup S) (⊥ : Subgroup S)).toEquiv, Nat.card_prod,
          Subgroup.card_bot, mul_one]
      rw [Nat.card_prod, Subgroup.card_top, h1, mul_one]

theorem s16c167_frame_le_relPPrimeCore {A : Type*} [Group A] {X Z : Subgroup A} (hZX : Z ≤ X)
    (hZn : ∀ x ∈ X, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z) (hodd : Odd (Nat.card Z)) :
    Z ≤ relPPrimeCore 2 X := by
  unfold relPPrimeCore
  refine le_sSup ⟨hZX, ?_, Nat.coprime_two_left.mpr hodd⟩
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using hZn (g : A) g.2 (n : A) hn

theorem s16c167_frame_relPPrimeCore_facts {A : Type*} [Group A] [Finite A] (X : Subgroup A) :
    relPPrimeCore 2 X ≤ X ∧
      (∀ x ∈ X, ∀ o ∈ relPPrimeCore 2 X, x * o * x⁻¹ ∈ relPPrimeCore 2 X) ∧
      Odd (Nat.card (relPPrimeCore 2 X)) := by
  refine ⟨relPPrimeCore_le X, ?_, ?_⟩
  · intro x hx o ho
    have hN := relPPrimeCore_normal (p := 2) Nat.prime_two X
    have hoX : o ∈ X := relPPrimeCore_le X ho
    have hconj := hN.conj_mem ⟨o, hoX⟩ (Subgroup.mem_subgroupOf.mpr ho) ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  · exact Nat.coprime_two_left.mp (coprime_card_relPPrimeCore (p := 2) Nat.prime_two X)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
