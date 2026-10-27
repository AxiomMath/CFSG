module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace Hat

theorem exists_central_ne_one {X : Type} [Group X] (h : Nat.card (Subgroup.center X) = 3) :
    ∃ c ∈ Subgroup.center X, c ≠ 1 := by
  by_contra hne
  have hbot : Subgroup.center X = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun c hc => by
    by_contra hc1
    exact hne ⟨c, hc, hc1⟩
  rw [hbot, Subgroup.card_bot] at h
  exact absurd h (by norm_num)

theorem exists_mulVec_ne {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {A : Matrix ι ι F} (hA : A ≠ 1) : ∃ v : ι → F, A.mulVec v ≠ v := by
  by_contra h
  refine hA (Matrix.ext_iff_mulVec.2 fun v => ?_)
  rw [Matrix.one_mulVec]
  by_contra hv
  exact h ⟨v, hv⟩

theorem realizes_nat_data {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι F)} (h : (FFModel.nat Γ₀).Realizes K ⊤ ⊥) :
    ∃ π : ↥Γ₀ →* ↥K, Function.Surjective π ∧
      ∀ γ : ↥Γ₀, π γ = 1 → ∀ v : ι → F,
        natAct Γ₀ γ (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
  obtain ⟨π, hsurj, -, -, -, -, -, -, β, hβs, -, hβe⟩ := h
  refine ⟨π, hsurj, fun γ h1' v => ?_⟩
  have h1 : π γ = 1 := h1'
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk
    (⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ : ↥(FFModel.nat Γ₀).sec))
  have hu' : ((π γ : ↥K) : MulAut W) (u : W) ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
  have hm' : natAct Γ₀ γ (Multiplicative.ofAdd v) ∈ (FFModel.nat Γ₀).sec := Subgroup.mem_top _
  have h2 := hβe γ u ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ hu' hm' hu
  have e : (⟨((π γ : ↥K) : MulAut W) (u : W), hu'⟩ : ↥(⊤ : Subgroup W)) = u :=
    Subtype.ext (by simp [h1])
  rw [e, hu, QuotientGroup.eq] at h2
  have h4 : (Multiplicative.ofAdd v)⁻¹ * natAct Γ₀ γ (Multiplicative.ofAdd v) = 1 :=
    Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h2)
  exact (inv_mul_eq_one.1 h4).symm

theorem false_of_realizes_nat {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι F)} (hK : IsSimpleGroup ↥K)
    (hnab : ∃ x y : ↥K, x * y ≠ y * x) (hc : ∃ c ∈ Subgroup.center ↥Γ₀, c ≠ 1)
    (h : (FFModel.nat Γ₀).Realizes K ⊤ ⊥) : False := by
  obtain ⟨π, hsurj, hact⟩ := realizes_nat_data h
  obtain ⟨c, hcZ, hc1⟩ := hc
  have hA : (((c : ↥Γ₀) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) ≠ 1 := by
    intro h1
    exact hc1 (Subtype.ext (Units.ext (by simpa using h1)))
  obtain ⟨v, hv⟩ := exists_mulVec_ne hA
  have hπ : π c ≠ 1 := fun h1 => hv (congrArg Multiplicative.toAdd (hact c h1 v))
  have hcen : π c ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨g, rfl⟩ := hsurj k
    calc π g * π c = π (g * c) := (map_mul π g c).symm
      _ = π (c * g) := by rw [Subgroup.mem_center_iff.1 hcZ g]
      _ = π c * π g := map_mul π c g
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with hb | ht
  · exact hπ (by simpa [hb] using hcen)
  · obtain ⟨x, y, hxy⟩ := hnab
    have hy : y ∈ Subgroup.center ↥K := ht ▸ Subgroup.mem_top y
    exact hxy (Subgroup.mem_center_iff.1 hy x)

theorem false_of_tripleA6Six {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    (hK : IsSimpleGroup ↥K) (hnab : ∃ x y : ↥K, x * y ≠ y * x) (h : TripleA6Six K ⊤ ⊥) :
    False := by
  obtain ⟨F, _, _, Γ₀, -, -, ⟨-, hcard, -⟩, -, hreal⟩ := h
  exact false_of_realizes_nat hK hnab (exists_central_ne_one hcard) hreal

theorem false_of_mhat22Twelve {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    (hK : IsSimpleGroup ↥K) (hnab : ∃ x y : ↥K, x * y ≠ y * x) (h : Mhat22Twelve K ⊤ ⊥) :
    False := by
  obtain ⟨F, _, _, Γ₀, -, ⟨-, hcard, -⟩, -, hreal⟩ := h
  exact false_of_realizes_nat hK hnab (exists_central_ne_one hcard) hreal

theorem oneHat_holds : OneHat := by
  intro W _ _ G₀ K S a z h hh
  rcases hh with hh | hh
  · exact false_of_tripleA6Six h.simple h.nab hh
  · exact false_of_mhat22Twelve h.simple h.nab hh

end Hat

end S153G93D

end CFSG.Quasithin
