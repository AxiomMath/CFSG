module

public import CFSG.Milestones.ASVolI.C41.Mod

public section

namespace CFSG.ASVolI

open CFSG.Open

variable {G : Type} [Group G] {F : Type} [Field F]

open scoped Classical in
noncomputable def burnsideC41b_conjCoord {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    (g : G) (v : Fin 3 → F) : Fin 3 → F :=
  if h : g * ((e.symm (Multiplicative.ofAdd v) : ↥W) : G) * g⁻¹ ∈ W then
    Multiplicative.toAdd (e ⟨_, h⟩) else 0

theorem burnsideC41b_exists_coord {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    (v : Fin 3 → F) : ∃ u : ↥W, Multiplicative.toAdd (e u) = v :=
  ⟨e.symm (Multiplicative.ofAdd v), by simp⟩

theorem burnsideC41b_conjCoord_spec {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    {g : G} (u v : ↥W) (huv : (v : G) = g * u * g⁻¹) :
    burnsideC41b_conjCoord e g (Multiplicative.toAdd (e u)) = Multiplicative.toAdd (e v) := by
  unfold burnsideC41b_conjCoord
  have h1 : e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e u))) = u := by simp
  have hmem : g * ((e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e u))) : ↥W) : G) *
      g⁻¹ ∈ W := by
    rw [h1, ← huv]
    exact v.2
  rw [dif_pos hmem]
  have h2 : (⟨_, hmem⟩ : ↥W) = v := by
    apply Subtype.ext
    show g * ((e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e u))) : ↥W) : G) * g⁻¹ =
      (v : G)
    rw [h1, huv]
  rw [h2]

theorem burnsideC41b_conj_mem {W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (u : ↥W) : g * (u : G) * g⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp hg u).mp u.2

theorem burnsideC41b_conjCoord_add {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) (v w : Fin 3 → F) :
    burnsideC41b_conjCoord e g (v + w) =
      burnsideC41b_conjCoord e g v + burnsideC41b_conjCoord e g w := by
  obtain ⟨u₁, rfl⟩ := burnsideC41b_exists_coord e v
  obtain ⟨u₂, rfl⟩ := burnsideC41b_exists_coord e w
  have hsum : Multiplicative.toAdd (e u₁) + Multiplicative.toAdd (e u₂) =
      Multiplicative.toAdd (e (u₁ * u₂)) := by rw [map_mul, toAdd_mul]
  rw [hsum,
    burnsideC41b_conjCoord_spec e (u₁ * u₂) ⟨_, burnsideC41b_conj_mem hg (u₁ * u₂)⟩ rfl,
    burnsideC41b_conjCoord_spec e u₁ ⟨_, burnsideC41b_conj_mem hg u₁⟩ rfl,
    burnsideC41b_conjCoord_spec e u₂ ⟨_, burnsideC41b_conj_mem hg u₂⟩ rfl, ← toAdd_mul,
    ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  group

theorem burnsideC41b_conjCoord_mul {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    {g h : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hh : h ∈ Subgroup.normalizer (W : Set G)) (v : Fin 3 → F) :
    burnsideC41b_conjCoord e (g * h) v =
      burnsideC41b_conjCoord e g (burnsideC41b_conjCoord e h v) := by
  obtain ⟨u, rfl⟩ := burnsideC41b_exists_coord e v
  set u' : ↥W := ⟨_, burnsideC41b_conj_mem hh u⟩ with hu'
  rw [burnsideC41b_conjCoord_spec e u u' rfl,
    burnsideC41b_conjCoord_spec e u' ⟨_, burnsideC41b_conj_mem hg u'⟩ rfl,
    burnsideC41b_conjCoord_spec e u ⟨_, burnsideC41b_conj_mem (Subgroup.mul_mem _ hg hh) u⟩ rfl]
  congr 2
  apply Subtype.ext
  simp only [hu']
  group

theorem burnsideC41b_conjCoord_one {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    (v : Fin 3 → F) : burnsideC41b_conjCoord e 1 v = v := by
  obtain ⟨u, rfl⟩ := burnsideC41b_exists_coord e v
  rw [burnsideC41b_conjCoord_spec e u u (by group)]

theorem burnsideC41b_conjCoord_pow {W : Subgroup G} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) (N : ℕ) (v : Fin 3 → F) :
    burnsideC41b_conjCoord e (g ^ N) v = (burnsideC41b_conjCoord e g)^[N] v := by
  induction N generalizing v with
  | zero => rw [pow_zero, burnsideC41b_conjCoord_one, Function.iterate_zero_apply]
  | succ N ih =>
    rw [pow_succ', burnsideC41b_conjCoord_mul e hg (Subgroup.pow_mem _ hg N), ih,
      Function.iterate_succ_apply']

theorem burnsideC41b_mem_centralizer_of_conjCoord {W : Subgroup G}
    (e : ↥W ≃* Multiplicative (Fin 3 → F)) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G))
    (h : ∀ v, burnsideC41b_conjCoord e g v = v) :
    g ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := h (Multiplicative.toAdd (e ⟨x, hx⟩))
  rw [burnsideC41b_conjCoord_spec e ⟨x, hx⟩ ⟨_, burnsideC41b_conj_mem hg ⟨x, hx⟩⟩ rfl] at h1
  have h2 : (⟨g * x * g⁻¹, burnsideC41b_conj_mem hg ⟨x, hx⟩⟩ : ↥W) = ⟨x, hx⟩ :=
    e.injective (Multiplicative.toAdd.injective h1)
  have h3 : g * x * g⁻¹ = x := congrArg Subtype.val h2
  calc x * g = g * x * g⁻¹ * g := by rw [h3]
    _ = g * x := by group

theorem burnsideC41b_conjCoord_equivariant {K W : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} (e : ↥W ≃* Multiplicative (Fin 3 → F))
    (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hβeq : ∀ (a : ↥K) (u v : ↥W), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (e v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u)))
    {g : G} (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) (v : Fin 3 → F) :
    burnsideC41b_conjCoord e g (((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
      ((α ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgK k).mp k.2⟩ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec (burnsideC41b_conjCoord e g v) := by
  obtain ⟨u, rfl⟩ := burnsideC41b_exists_coord e v
  set k' : ↥K := ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgK k).mp k.2⟩ with hk'
  set ku : ↥W := ⟨_, burnsideC41b_conj_mem (hKW k.2) u⟩ with hku
  set gu : ↥W := ⟨_, burnsideC41b_conj_mem hgW u⟩ with hgu
  set gku : ↥W := ⟨_, burnsideC41b_conj_mem hgW ku⟩ with hgku
  rw [← hβeq k u ku rfl, burnsideC41b_conjCoord_spec e ku gku rfl,
    burnsideC41b_conjCoord_spec e u gu rfl]
  refine hβeq k' gu gku ?_
  simp only [hk', hku, hgu, hgku, InvMemClass.coe_inv]
  group

theorem burnsideC41b_relIndex_le_sq [Finite G] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {K W R P V₁ : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (e : ↥W ≃* Multiplicative (Fin 3 → F))
    (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hβeq : ∀ (a : ↥K) (u v : ↥W), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (e v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u)))
    (W₀ : Submodule F (Fin 3 → F)) (hW₀ : Module.finrank F W₀ = 2)
    (hV₁ : ∀ u : ↥W, (u : G) ∈ V₁ ↔ Multiplicative.toAdd (e u) ∈ W₀)
    (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hRV : ∀ r ∈ R, ∀ x ∈ V₁, r * x = x * r) (hR2 : IsPGroup 2 R)
    (hCP : ∀ r ∈ R, r ∈ Subgroup.centralizer (W : Set G) → r ∈ P) :
    P.relIndex R ≤ Fintype.card F ^ 2 := by
  classical
  let θ : ↥R → (Fin 3 → F) →+ (Fin 3 → F) := fun r =>
    AddMonoidHom.mk' (burnsideC41b_conjCoord e (r : G)) (burnsideC41b_conjCoord_add e (hRW r.2))
  have hθ : ∀ r v, θ r v = burnsideC41b_conjCoord e (r : G) v := fun _ _ => rfl
  have hfix : ∀ r : ↥R, ∀ w ∈ W₀, burnsideC41b_conjCoord e (r : G) w = w := by
    intro r w hw
    obtain ⟨u, rfl⟩ := burnsideC41b_exists_coord e w
    have huV : (u : G) ∈ V₁ := (hV₁ u).mpr hw
    exact burnsideC41b_conjCoord_spec e u u (by rw [hRV r r.2 u huV, mul_inv_cancel_right])
  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w ∈ W₀, w ≠ 0 := by
    have hne : W₀ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW₀
      exact absurd hW₀ (by norm_num)
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hNorm : ∀ g : G, g ∈ R → ∀ γ : ↥(StatedSL 3 F), ∃ γ' : ↥(StatedSL 3 F), ∀ v,
      burnsideC41b_conjCoord e g (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((γ' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (burnsideC41b_conjCoord e g v) := by
    intro g hg γ
    obtain ⟨k, rfl⟩ := hα γ
    exact ⟨_, burnsideC41b_conjCoord_equivariant e hKW hβeq (hRW hg) (hRK hg) k⟩
  have hlin : ∀ (r : ↥R) (c : F) (v : Fin 3 → F),
      burnsideC41b_conjCoord e (r : G) (c • v) = c • burnsideC41b_conjCoord e (r : G) v := by
    intro r c v
    have hr' : (r : G)⁻¹ ∈ R := R.inv_mem r.2
    refine burnsideC41b_smul_of_normalizes (θ r) (θ ⟨_, hr'⟩) ?_ ?_ (hNorm _ r.2)
      (hNorm _ hr') hw₀0 ?_ c v
    · intro v
      rw [hθ, hθ, ← burnsideC41b_conjCoord_mul e (hRW r.2) (hRW hr'), mul_inv_cancel,
        burnsideC41b_conjCoord_one]
    · intro v
      rw [hθ, hθ, ← burnsideC41b_conjCoord_mul e (hRW hr') (hRW r.2), inv_mul_cancel,
        burnsideC41b_conjCoord_one]
    · intro c
      exact hfix r _ (W₀.smul_mem c hw₀)
  let θL : ↥R → (Fin 3 → F) →ₗ[F] (Fin 3 → F) := fun r =>
    { toFun := burnsideC41b_conjCoord e (r : G)
      map_add' := burnsideC41b_conjCoord_add e (hRW r.2)
      map_smul' := hlin r }
  have hθL : ∀ r v, θL r v = burnsideC41b_conjCoord e (r : G) v := fun _ _ => rfl
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin 3 → F, e₀ ∉ W₀ := by
    by_contra h
    push Not at h
    have htop : W₀ = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, finrank_top, Module.finrank_fin_fun] at hW₀
    exact absurd hW₀ (by norm_num)
  have hψ : ∀ r : ↥R, burnsideC41b_conjCoord e (r : G) e₀ - e₀ ∈ W₀ := by
    intro r
    obtain ⟨m, hm⟩ := hR2 r
    have hrm : (r : G) ^ (2 ^ m) = 1 := by
      have h := congrArg Subtype.val hm
      simpa using h
    refine burnsideC41b_sub_mem_of_iterate W₀ hW₀ he₀ (θL r) (fun w hw => hfix r w hw)
      (N := 2 ^ m) ?_ (fun d hd => burnsideC41b_eq_one_of_pow_two_pow hF hd)
    have h1 : (⇑(θL r))^[2 ^ m] = (burnsideC41b_conjCoord e (r : G))^[2 ^ m] := rfl
    rw [h1, ← burnsideC41b_conjCoord_pow e (hRW r.2), hrm, burnsideC41b_conjCoord_one]
  have hinj : ∀ r r' : ↥R,
      burnsideC41b_conjCoord e (r : G) e₀ = burnsideC41b_conjCoord e (r' : G) e₀ →
        ((r⁻¹ * r' : ↥R) : G) ∈ P := by
    intro r r' h
    have hEq : θL r = θL r' :=
      burnsideC41b_linearMap_eq W₀ hW₀ he₀
        (fun w hw => by rw [hθL, hθL, hfix r w hw, hfix r' w hw]) h
    have hr' : (r : G)⁻¹ ∈ R := R.inv_mem r.2
    have hall : ∀ v, burnsideC41b_conjCoord e ((r⁻¹ * r' : ↥R) : G) v = v := by
      intro v
      rw [Subgroup.coe_mul, InvMemClass.coe_inv,
        burnsideC41b_conjCoord_mul e (hRW hr') (hRW r'.2), ← hθL r' v, ← hEq, hθL,
        ← burnsideC41b_conjCoord_mul e (hRW hr') (hRW r.2), inv_mul_cancel,
        burnsideC41b_conjCoord_one]
    exact hCP _ (r⁻¹ * r').2
      (burnsideC41b_mem_centralizer_of_conjCoord e (hRW (r⁻¹ * r').2) hall)
  let f : ↥R ⧸ P.subgroupOf R → ↥W₀ := fun q => ⟨_, hψ q.out⟩
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    have h1 : burnsideC41b_conjCoord e ((q₁.out : ↥R) : G) e₀ =
        burnsideC41b_conjCoord e ((q₂.out : ↥R) : G) e₀ :=
      sub_left_inj.mp (congrArg Subtype.val hq)
    have h2 := hinj _ _ h1
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr h2
  have hcard := Nat.card_le_card_of_injective f hf
  have hW₀card : Nat.card ↥W₀ = Fintype.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hW₀, Nat.card_eq_fintype_card]
  rw [hW₀card] at hcard
  exact hcard

end CFSG.ASVolI
