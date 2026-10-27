module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.CTP

@[expose] def fixUnion {K : Type*} [Group K] (E : Subgroup (MulAut K)) : Set K :=
  {k | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k = k}

section Generic

variable {K : Type*} [Group K]

theorem conj_injective_of_simple [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  have hz : g ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 : g * h * g⁻¹ = h := by
      simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut K => φ h) hg
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact hne (by simpa [h] using hz)
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center K := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem centralizers_subset_fixUnion (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (E : Subgroup (MulAut K)) :
    {k : K | ∃ x ∈ E.comap (MulAut.conj : K →* MulAut K), x ≠ 1 ∧ k * x = x * k} ⊆
      fixUnion E := by
  rintro k ⟨x, hxE, hx1, hk⟩
  refine ⟨Subgroup.zpowers (MulAut.conj x), ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact hxE
  · intro hbot
    have hmem : MulAut.conj x ∈ (⊥ : Subgroup (MulAut K)) := hbot ▸ Subgroup.mem_zpowers _
    exact hx1 (hinj (by simpa using hmem))
  · intro φ hφ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφ
    have hc : Commute k (x ^ n) := (show Commute k x from hk).zpow_right n
    rw [← map_zpow, MulAut.conj_apply]
    calc x ^ n * k * (x ^ n)⁻¹ = k * x ^ n * (x ^ n)⁻¹ := by rw [hc.eq]
      _ = k := by group

theorem inner_preimage_data {p : ℕ} [Fact p.Prime]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (E : Subgroup (MulAut K))
    [CFSG.IsElementaryAbelian p E] (hinner : ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) :
    CFSG.IsElementaryAbelian p (E.comap (MulAut.conj : K →* MulAut K)) ∧
      (E.comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) = E := by
  refine ⟨?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · have h := congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨MulAut.conj (a : K), a.2⟩ : E) ⟨MulAut.conj (b : K), b.2⟩)
      refine Subtype.ext (hinj ?_)
      change MulAut.conj ((a : K) * b) = MulAut.conj ((b : K) * a)
      rw [map_mul, map_mul]
      exact h
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      refine Subtype.ext (hinj ?_)
      change MulAut.conj ((x : K) ^ p) = MulAut.conj 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ x.2
  · ext φ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hφ
      obtain ⟨g, rfl⟩ := hinner φ hφ
      exact ⟨g, hφ, rfl⟩

end Generic

section Transfer

variable {K P : Type*} [Group K] [Group P]

theorem closure_centralizers_transfer (e : K ≃* P) (E₀ : Subgroup K)
    (h : Subgroup.closure {k' : P | ∃ x ∈ E₀.map e.toMonoidHom, x ≠ 1 ∧ k' * x = x * k'} = ⊤) :
    Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hsub : {k' : P | ∃ x ∈ E₀.map e.toMonoidHom, x ≠ 1 ∧ k' * x = x * k'} ⊆
      e.toMonoidHom '' {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} := by
    rintro k' ⟨_, ⟨x, hx, rfl⟩, hx1, hk⟩
    refine ⟨e.symm k', ⟨x, hx, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hk
  have hle : (⊤ : Subgroup P) ≤
      (Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, ← h]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro k _
  obtain ⟨c, hc, hck⟩ := hle (Subgroup.mem_top (e k))
  have : c = k := e.injective hck
  exact this ▸ hc

end Transfer

theorem closure_fixUnion_eq_top_of_inner_equiv {K P : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a) [Group P] (e : K ≃* P) {p : ℕ}
    [Fact p.Prime]
    (hP : ∀ E₁ : Subgroup P, CFSG.IsElementaryAbelian p E₁ → Nat.card E₁ = p ^ 2 →
      Subgroup.closure {k' : P | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤)
    (E : Subgroup (MulAut K)) [CFSG.IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2)
    (hinner : ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  have hinj := conj_injective_of_simple hnab
  obtain ⟨hE₀, hmap⟩ := inner_preimage_data (p := p) hinj E hinner
  have hcard : Nat.card (E.comap (MulAut.conj : K →* MulAut K)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hE
  have hE₁ : CFSG.IsElementaryAbelian p ((E.comap (MulAut.conj : K →* MulAut K)).map
      e.toMonoidHom) := CFSG.IsElementaryAbelian.map _
  have hcard₁ : Nat.card ((E.comap (MulAut.conj : K →* MulAut K)).map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  have h2 := closure_centralizers_transfer e _ (hP _ hE₁ hcard₁)
  rw [eq_top_iff, ← h2]
  exact Subgroup.closure_mono (centralizers_subset_fixUnion hinj E)

end CFSG.RankThree.PartOne.CTP
