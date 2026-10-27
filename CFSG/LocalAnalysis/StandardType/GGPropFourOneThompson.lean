module

public import CFSG.LocalAnalysis.StandardType.GGPropFourOneTransfer
public import CFSG.LocalAnalysis.StandardType.GGOneFiveRank
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem3_1

public section

namespace CFSG.StandardType

open CFSG

variable {G : Type*} [Group G]

theorem isMulCommutative_map {H : Subgroup G} (hH : IsMulCommutative H) {K : Type*} [Group K]
    (f : G →* K) : IsMulCommutative (H.map f) :=
  ⟨⟨fun ⟨_, a, ha, hfa⟩ ⟨_, b, hb, hfb⟩ => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hfa, ← hfb, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hH.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))⟩⟩

theorem thompsonAbelianSubgroups_eq_of_replacement [Finite G] {p : ℕ} [Fact p.Prime]
    {R U U₁ : Subgroup G} (hR : IsPGroup p R) (hUR : U ≤ R) (hU₁U : U₁ ≤ U)
    (hU₁R : R ≤ Subgroup.normalizer (U₁ : Set G)) (hU₁ab : IsMulCommutative U₁)
    (hJU : ∀ A ∈ thompsonAbelianSubgroups U, A = U₁)
    (hrep : ∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U) :
    ∀ A ∈ thompsonAbelianSubgroups R, A = U₁ := by
  suffices h : ∀ n : ℕ, ∀ A ∈ thompsonAbelianSubgroups R,
      Nat.card U₁ - Nat.card (A ⊓ U₁ : Subgroup G) = n → A = U₁ from
    fun A hA => h _ A hA rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hn
    by_cases hAAA : ⁅⁅U₁, A⁆, A⁆ = ⊥
    · exact hJU A (thompsonAbelianSubgroups_mem_of_le hUR hA (hrep A hA hAAA))
    · obtain ⟨Astar, hAstar, hlt, hAAs⟩ :=
        Glauberman.theorem3_1b hR hA (hU₁U.trans hUR) hU₁ab (hA.1.trans hU₁R) hAAA
      by_cases hAs : Astar = U₁
      · exact absurd (hAs ▸ hAAs) hAAA
      · have hlt' := Subgroup.card_lt_of_lt hlt
        have hle : Nat.card (Astar ⊓ U₁ : Subgroup G) ≤ Nat.card U₁ :=
          Subgroup.card_le_of_le inf_le_right
        exact absurd (ih _ (by omega) Astar hAstar rfl) hAs

theorem mem_thompsonAbelianSubgroups_of_forall_eq [Finite G] {R U₁ : Subgroup G}
    (h : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) : U₁ ∈ thompsonAbelianSubgroups R := by
  obtain ⟨A, hA⟩ := thompsonAbelianSubgroups_nonempty R
  exact h A hA ▸ hA

theorem thompsonSubgroup_eq_of_forall_eq [Finite G] {R U₁ : Subgroup G}
    (h : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) : thompsonSubgroup R = U₁ :=
  le_antisymm (sSup_le fun A hA => (h A hA).le)
    (le_sSup (mem_thompsonAbelianSubgroups_of_forall_eq h))

theorem ggWeaklyClosed_of_forall_eq [Finite G] {R U₁ : Subgroup G}
    (h : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) : GGWeaklyClosed U₁ R := by
  have hU₁ := mem_thompsonAbelianSubgroups_of_forall_eq h
  intro g hg u hu
  let A : Subgroup G := U₁.map (MulAut.conj g⁻¹).toMonoidHom
  have hAR : A ≤ R := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using hg v hv
  have hcard : Nat.card A = Nat.card U₁ :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hAmem : A ∈ thompsonAbelianSubgroups R :=
    ⟨hAR, isMulCommutative_map hU₁.2.1 _, fun B hBR hBab => hcard ▸ hU₁.2.2 B hBR hBab⟩
  have hmem : g⁻¹ * u * g ∈ A := ⟨u, hu, by simp⟩
  rwa [h A hAmem] at hmem

theorem normalizer_le_normalizer_of_ggWeaklyClosed [Finite G] {W R : Subgroup G}
    (hW : GGWeaklyClosed W R) (hWR : W ≤ R) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (W : Set G) := by
  intro g hg
  refine hW.mem_normalizer fun w hw => ?_
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp (hWR hw)
  simpa using this

theorem normalizer_le_normalizer_of_forall_eq [Finite G] {U U₁ : Subgroup G}
    (h : ∀ A ∈ thompsonAbelianSubgroups U, A = U₁) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (U₁ : Set G) :=
  normalizer_le_normalizer_of_ggWeaklyClosed (ggWeaklyClosed_of_forall_eq h)
    (mem_thompsonAbelianSubgroups_of_forall_eq h).1

theorem normalizer_le_normalizer_of_mem_iff {p : ℕ} {U₁ B₁ : Subgroup G}
    (hB₁ : ∀ u : G, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1) :
    Subgroup.normalizer (U₁ : Set G) ≤ Subgroup.normalizer (B₁ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  rw [hB₁, hB₁, hg h, conj_pow]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, mul_one, mul_inv_cancel]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg (fun y => g⁻¹ * y * g) h2
    simpa [mul_assoc] using this

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG

variable {G : Type} [Group G]

theorem ggL47 [Finite G] {p : ℕ} [Fact p.Prime] {M R U U₁ B₁ : Subgroup G}
    (hR : IsPGroup p R) (hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → R ≤ Q → Q = R)
    (hUR : U ≤ R) (hRU : R ≤ Subgroup.normalizer (U : Set G)) (hU₁U : U₁ ≤ U)
    (hU₁ab : IsMulCommutative U₁) (hJU : ∀ A ∈ thompsonAbelianSubgroups U, A = U₁)
    (hB₁ : ∀ u : G, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1)
    (hB₁M : Subgroup.normalizer (B₁ : Set G) ≤ M)
    (hrep : ∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U) :
    (∃ S : Sylow p G, (S : Subgroup G) = R) ∧ thompsonSubgroup R = U₁ ∧
      GGWeaklyClosed U₁ R := by
  have hU₁R : R ≤ Subgroup.normalizer (U₁ : Set G) :=
    hRU.trans (normalizer_le_normalizer_of_forall_eq hJU)
  have hA := thompsonAbelianSubgroups_eq_of_replacement hR hUR hU₁U hU₁R hU₁ab hJU hrep
  have hwc := ggWeaklyClosed_of_forall_eq hA
  have hN : Subgroup.normalizer (R : Set G) ≤ M :=
    ((normalizer_le_normalizer_of_ggWeaklyClosed hwc (hU₁U.trans hUR)).trans
      (normalizer_le_normalizer_of_mem_iff hB₁)).trans hB₁M
  exact ⟨⟨{ toSubgroup := R
            isPGroup' := hR
            is_maximal' := fun {Q} hQ hRQ => isMaxPSubgroup_of_normalizer_le hmax hN Q hQ hRQ },
          rfl⟩, thompsonSubgroup_eq_of_forall_eq hA, hwc⟩

end CFSG.StandardType

end
