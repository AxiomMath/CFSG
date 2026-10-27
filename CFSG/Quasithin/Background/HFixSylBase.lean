module

public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.Quasithin.H.FixSyl

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem card_fixV_le_of_isPGroup [Finite V] {H S P : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hPH : P ≤ H)
    (hP : IsPGroup 2 ↥P) : Nat.card ↥(fixV S) ≤ Nat.card ↥(fixV P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  let T : Sylow 2 ↥H := Sylow.ofCard (S.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
    exact hS)
  have hP' : IsPGroup 2 ↥(P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H T Q
  have key : ∀ x ∈ P, (g : MulAut V)⁻¹ * x * g ∈ S := by
    intro x hx
    have h1 : (⟨x, hPH hx⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.2 hx)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using h2
  refine Nat.card_le_card_of_injective
    (fun v : ↥(fixV S) => (⟨(g : MulAut V) v, fun x hx => ?_⟩ : ↥(fixV P))) ?_
  · have h3 : (g : MulAut V)⁻¹ (x ((g : MulAut V) v)) = v := v.2 _ (key x hx)
    calc x ((g : MulAut V) v)
        = (g : MulAut V) ((g : MulAut V)⁻¹ (x ((g : MulAut V) v))) :=
          (MulEquiv.apply_symm_apply _ _).symm
      _ = (g : MulAut V) v := by rw [h3]
  · intro v w hvw
    exact Subtype.ext ((g : MulAut V).injective (congrArg Subtype.val hvw))

theorem card_fixV_le_of_le_map [Finite V] (e : V ≃* W) {H S : Subgroup (MulAut V)}
    {P : Subgroup (MulAut W)} (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hPH : P ≤ H.map (congrHom e))
    (hP : IsPGroup 2 ↥P) : Nat.card ↥(fixV S) ≤ Nat.card ↥(fixV P) := by
  obtain ⟨P₀, hP₀H, rfl⟩ := exists_eq_map_congrHom e hPH
  have hP₀ : IsPGroup 2 ↥P₀ :=
    hP.of_equiv (Subgroup.equivMapOfInjective P₀ (congrHom e) (congrHom_injective e)).symm
  rw [fixV_map_congrHom, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact card_fixV_le_of_isPGroup hSH hS hP₀H hP₀

theorem card_le_two_of_forall {K : Subgroup W} (w₀ : W) (h : ∀ w ∈ K, w = 1 ∨ w = w₀) :
    Nat.card ↥K ≤ 2 := by
  classical
  have hf : Function.Injective fun w : ↥K => decide ((w : W) = 1) := by
    intro a b hab
    apply Subtype.ext
    by_cases ha : (a : W) = 1 <;> by_cases hb : (b : W) = 1
    · rw [ha, hb]
    · simp [ha, hb] at hab
    · simp [ha, hb] at hab
    · rw [(h a a.2).resolve_left ha, (h b b.2).resolve_left hb]
  simpa using Nat.card_le_card_of_injective _ hf

theorem isPGroup_closure_of_commute {G : Type*} [Group G] {s : Set G}
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (hs : ∀ a ∈ s, a * a = 1) :
    IsPGroup 2 ↥(Subgroup.closure s) := by
  have h1 : Subgroup.closure s ≤ Subgroup.centralizer s :=
    (Subgroup.closure_le _).2 fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun b hb => hc b hb a ha
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s : Set G) :=
    (Subgroup.closure_le _).2 fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun b hb =>
        (Subgroup.mem_centralizer_iff.1 (h1 hb) a ha).symm
  have hsq : ∀ a ∈ Subgroup.closure s, a * a = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hs x hx
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := Subgroup.mem_centralizer_iff.1 (h2 hy) x hx
      calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * x * (y * y) := by rw [← hxy]; simp only [mul_assoc]
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ih => rw [← mul_inv_rev, ih, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq g g.2)⟩

theorem card_fixV_le_two_of_gens [Finite V] (e : V ≃* W) {H S : Subgroup (MulAut V)}
    (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    {s : Set (MulAut W)} (hsH : s ⊆ H.map (congrHom e))
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (hs : ∀ a ∈ s, a * a = 1) (w₀ : W)
    (hfix : ∀ w : W, (∀ a ∈ s, a w = w) → w = 1 ∨ w = w₀) :
    Nat.card ↥(fixV S) ≤ 2 :=
  (card_fixV_le_of_le_map e hSH hS ((Subgroup.closure_le _).2 hsH)
    (isPGroup_closure_of_commute hc hs)).trans
    (card_le_two_of_forall w₀ fun w hw => hfix w fun a ha => hw a (Subgroup.subset_closure ha))

end CFSG.Quasithin.H.FixSyl
