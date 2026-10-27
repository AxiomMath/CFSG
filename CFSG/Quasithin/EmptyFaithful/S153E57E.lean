module

public import CFSG.Quasithin.EmptyFaithful.S153E57D
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E57

theorem conj_mem_sup {Γ : Type*} [Group Γ] {S₁ S₂ : Subgroup Γ} (g : Γ)
    (h₁ : ∀ a ∈ S₁, g * a * g⁻¹ ∈ S₁ ⊔ S₂) (h₂ : ∀ a ∈ S₂, g * a * g⁻¹ ∈ S₁ ⊔ S₂) :
    ∀ a ∈ S₁ ⊔ S₂, g * a * g⁻¹ ∈ S₁ ⊔ S₂ := by
  have : S₁ ⊔ S₂ ≤ (S₁ ⊔ S₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => h₁ a ha) (fun a ha => h₂ a ha)
  exact fun a ha => this ha

theorem mem_normalizer_sup {Γ : Type*} [Group Γ] {S₁ S₂ : Subgroup Γ} (g : Γ)
    (h₁ : ∀ a ∈ S₁, g * a * g⁻¹ ∈ S₁ ⊔ S₂) (h₂ : ∀ a ∈ S₂, g * a * g⁻¹ ∈ S₁ ⊔ S₂)
    (h₃ : ∀ a ∈ S₁, g⁻¹ * a * g⁻¹⁻¹ ∈ S₁ ⊔ S₂) (h₄ : ∀ a ∈ S₂, g⁻¹ * a * g⁻¹⁻¹ ∈ S₁ ⊔ S₂) :
    g ∈ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact fun ha => conj_mem_sup g h₁ h₂ a ha
  · intro ha
    have := conj_mem_sup g⁻¹ h₃ h₄ _ ha
    simpa [mul_assoc] using this

section Chain

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem t₁_mem_NZ (cx : Ctx15350 T Mc M V₁ V₂ t) (ht₁ : t₁ ∈ T) : t₁ ∈ NZ T :=
  Mc_le_NZ cx (S153E.T_le_Mc cx ht₁)

@[expose] noncomputable def ttOf (cx : Ctx15350 T Mc M V₁ V₂ t) (ht₁ : t₁ ∈ T) :
    MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  rho cx ⟨t₁, t₁_mem_NZ cx ht₁⟩

noncomputable abbrev XS (T M V₁ Mc : Subgroup G) (y : G) :
    Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :=
  XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)

noncomputable abbrev XS' (T M V₁ Mc : Subgroup G) (y t₁ : G) :
    Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :=
  XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)

theorem mem_XS'_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (ht₁ : t₁ ∈ T)
    (a' : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    a' ∈ XS' T M V₁ Mc y t₁ ↔ ∃ a ∈ XS T M V₁ Mc y, a' = (ttOf cx ht₁)⁻¹ * a * ttOf cx ht₁ :=
  mem_XStar_conj_iff cx _ ⟨t₁, t₁_mem_NZ cx ht₁⟩ a'

theorem tt_sq_eq (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ∃ c' : NZ T, (c' : G) ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
      ttOf cx c.ht₁.1 * ttOf cx c.ht₁.1 = rho cx c' := by
  obtain ⟨u, huU, c', hc', hsq⟩ := sq_mem_UCT cx c.h51 c.h52 c.ht₁.1
  have hc'N : c' ∈ NZ T := Mc_le_NZ cx (S153E.T_le_Mc cx hc'.1)
  have huN : u ∈ NZ T := Mc_le_NZ cx (S153E.T_le_Mc cx (S153E.U_le_T cx huU))
  refine ⟨⟨c', hc'N⟩, hc', ?_⟩
  unfold ttOf
  rw [← map_mul]
  have e : (⟨t₁, t₁_mem_NZ cx c.ht₁.1⟩ * ⟨t₁, t₁_mem_NZ cx c.ht₁.1⟩ : NZ T) =
      ⟨u, huN⟩ * ⟨c', hc'N⟩ := Subtype.ext hsq
  rw [e, map_mul, rho_eq_one_of_mem_U cx ⟨u, huN⟩ huU, one_mul]

theorem tt_sq_conj_mem (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    (∀ a ∈ XS T M V₁ Mc y, (ttOf cx c.ht₁.1 * ttOf cx c.ht₁.1) * a *
        (ttOf cx c.ht₁.1 * ttOf cx c.ht₁.1)⁻¹ ∈ XS T M V₁ Mc y) ∧
      ∀ a ∈ XS T M V₁ Mc y, (ttOf cx c.ht₁.1 * ttOf cx c.ht₁.1)⁻¹ * a *
        (ttOf cx c.ht₁.1 * ttOf cx c.ht₁.1) ∈ XS T M V₁ Mc y := by
  obtain ⟨c', hc', htt⟩ := tt_sq_eq cx c
  rw [htt]
  have hy := c.hy.1
  constructor
  · intro a ha
    obtain ⟨n, hnX, rfl⟩ := (mem_XStar_iff cx _ _).1 ha
    have hmem := conj_normalizes_X cx hy hc' _ hnX
    have e : rho cx c' * rho cx n * (rho cx c')⁻¹ = rho cx (c' * n * c'⁻¹) := by
      simp [map_mul, map_inv]
    rw [e]
    exact rho_mem_XStar cx _ (by simpa using hmem)
  · intro a ha
    obtain ⟨n, hnX, rfl⟩ := (mem_XStar_iff cx _ _).1 ha
    have hc'inv : ((c'⁻¹ : NZ T) : G) ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      have := (T ⊓ Subgroup.centralizer (VZ T M : Set G)).inv_mem hc'
      simpa using this
    have hmem := conj_normalizes_X cx hy hc'inv _ hnX
    have e : (rho cx c')⁻¹ * rho cx n * rho cx c' = rho cx (c'⁻¹ * n * c'⁻¹⁻¹) := by
      simp [map_mul, map_inv]
    rw [e]
    exact rho_mem_XStar cx _ (by simpa using hmem)

theorem tt_mem_normalizer (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ttOf cx c.ht₁.1 ∈ Subgroup.normalizer
      ((XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁ : Subgroup _) : Set _) := by
  have ht := c.ht₁.1
  obtain ⟨hsq₁, hsq₂⟩ := tt_sq_conj_mem cx c
  refine mem_normalizer_sup _ ?_ ?_ ?_ ?_
  · intro a ha
    refine Subgroup.mem_sup_right ((mem_XS'_iff cx ht _).2 ⟨_, hsq₁ a ha, ?_⟩)
    group
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_XS'_iff cx ht _).1 ha'
    have : ttOf cx ht * ((ttOf cx ht)⁻¹ * a * ttOf cx ht) * (ttOf cx ht)⁻¹ = a := by group
    rw [this]
    exact Subgroup.mem_sup_left ha
  · intro a ha
    exact Subgroup.mem_sup_right ((mem_XS'_iff cx ht _).2 ⟨a, ha, by simp⟩)
  · intro a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_XS'_iff cx ht _).1 ha'
    have h := hsq₂ a ha
    have : (ttOf cx ht)⁻¹ * ((ttOf cx ht)⁻¹ * a * ttOf cx ht) * (ttOf cx ht)⁻¹⁻¹ =
        (ttOf cx ht * ttOf cx ht)⁻¹ * a * (ttOf cx ht * ttOf cx ht) := by group
    rw [this]
    exact Subgroup.mem_sup_left h

theorem isPGroup_A (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    IsPGroup 2 ↥(XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁) := by
  rcases c.h56.D8s with ⟨-, h⟩ | ⟨-, h⟩
  · exact IsPGroup.of_card (n := 1) (by simpa using h)
  · exact IsPGroup.of_card h.2.1

theorem isPGroup_zpowers_tt (cx : Ctx15350 T Mc M V₁ V₂ t) (ht₁ : t₁ ∈ T) :
    IsPGroup 2 ↥(Subgroup.zpowers (ttOf cx ht₁)) := by
  obtain ⟨k, hk⟩ := cx.hF.sylow.2.1 ⟨t₁, ht₁⟩
  have h1 : t₁ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : ttOf cx ht₁ ^ 2 ^ k = 1 := by
    unfold ttOf
    rw [← map_pow]
    have : (⟨t₁, t₁_mem_NZ cx ht₁⟩ : NZ T) ^ 2 ^ k = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  intro x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h2, one_zpow]

variable {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem exists_v (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ∃ v ∈ XStar153 T M V₁ Mc (VZ T M), v ≠ 1 ∧
      ∀ w ∈ XStar153 T M V₁ Mc (VZ T M), w = 1 ∨ w = v := by
  obtain ⟨w₀, hw₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(XStar153 T M V₁ Mc (VZ T M)))).1
    c.h56.card_Vstar
  refine ⟨(w₀ : MulAut _), w₀.2, fun h => hw₀ (Subtype.ext h), fun w hw => ?_⟩
  by_cases h1 : w = 1
  · exact Or.inl h1
  · right
    have := huniq ⟨w, hw⟩ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem Vs_le_XS (c : Chain15356 cx N₁ N₂ g s y t₁) :
    XStar153 T M V₁ Mc (VZ T M) ≤ XS T M V₁ Mc y := by
  rw [← c.h56.inter]
  exact inf_le_left

theorem Vs_le_XS' (c : Chain15356 cx N₁ N₂ g s y t₁) :
    XStar153 T M V₁ Mc (VZ T M) ≤ XS' T M V₁ Mc y t₁ := by
  rw [← c.h56.inter]
  exact inf_le_right

theorem XS_comm (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ∀ a ∈ XS T M V₁ Mc y, ∀ b ∈ XS T M V₁ Mc y, a * b = b * a := by
  obtain ⟨e⟩ := c.h56.X_rank
  intro a ha b hb
  have h : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (e.injective h)

theorem A_comm_v (c : Chain15356 cx N₁ N₂ g s y t₁) {v : MulAut _}
    (hv : v ∈ XStar153 T M V₁ Mc (VZ T M)) :
    ∀ d ∈ XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁, d * v = v * d := by
  have hvX : v ∈ XS T M V₁ Mc y := Vs_le_XS c hv
  have hvX' : v ∈ XS' T M V₁ Mc y t₁ := Vs_le_XS' c hv
  have h1 : XS T M V₁ Mc y ≤ Subgroup.centralizer ({v} : Set (MulAut _)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact XS_comm c v hvX a ha
  have h2 : XS' T M V₁ Mc y t₁ ≤ Subgroup.centralizer ({v} : Set (MulAut _)) := by
    intro a' ha'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    obtain ⟨a, ha, rfl⟩ := (mem_XS'_iff cx c.ht₁.1 _).1 ha'
    obtain ⟨b, hb, hbv⟩ := (mem_XS'_iff cx c.ht₁.1 _).1 hvX'
    rw [hbv]
    have := XS_comm c b hb a ha
    calc (ttOf cx c.ht₁.1)⁻¹ * b * ttOf cx c.ht₁.1 * ((ttOf cx c.ht₁.1)⁻¹ * a * ttOf cx c.ht₁.1)
        = (ttOf cx c.ht₁.1)⁻¹ * (b * a) * ttOf cx c.ht₁.1 := by group
      _ = (ttOf cx c.ht₁.1)⁻¹ * (a * b) * ttOf cx c.ht₁.1 := by rw [this]
      _ = (ttOf cx c.ht₁.1)⁻¹ * a * ttOf cx c.ht₁.1 * ((ttOf cx c.ht₁.1)⁻¹ * b * ttOf cx c.ht₁.1) := by
        group
  intro d hd
  have := sup_le h1 h2 hd
  exact (Subgroup.mem_centralizer_iff.1 this v (Set.mem_singleton v)).symm

theorem tt_comm_v (c : Chain15356 cx N₁ N₂ g s y t₁) {v : MulAut _}
    (hv : v ∈ XStar153 T M V₁ Mc (VZ T M)) (hv1 : v ≠ 1)
    (hvuniq : ∀ w ∈ XStar153 T M V₁ Mc (VZ T M), w = 1 ∨ w = v) :
    ttOf cx c.ht₁.1 * v = v * ttOf cx c.ht₁.1 := by
  have ht := c.ht₁.1
  obtain ⟨n, hnV, rfl⟩ := (mem_XStar_iff cx _ _).1 hv
  have htN : t₁ ∈ Subgroup.normalizer (VZ T M : Set G) := S153E.T_le_N cx ht
  have hmem : t₁ * (n : G) * t₁⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.1 htN _).1 hnV
  have h2 : ttOf cx ht * rho cx n * (ttOf cx ht)⁻¹ = rho cx (⟨t₁, t₁_mem_NZ cx ht⟩ * n *
      ⟨t₁, t₁_mem_NZ cx ht⟩⁻¹) := by
    unfold ttOf
    simp [map_mul, map_inv]
  have hVs : ttOf cx ht * rho cx n * (ttOf cx ht)⁻¹ ∈ XStar153 T M V₁ Mc (VZ T M) := by
    rw [h2]
    exact rho_mem_XStar cx _ (by simpa using hmem)
  rcases hvuniq _ hVs with h | h
  · exfalso
    apply hv1
    have : rho cx n = (ttOf cx ht)⁻¹ * (ttOf cx ht * rho cx n * (ttOf cx ht)⁻¹) * ttOf cx ht := by
      group
    rw [this, h]
    group
  · calc ttOf cx ht * rho cx n = (ttOf cx ht * rho cx n * (ttOf cx ht)⁻¹) * ttOf cx ht := by group
      _ = rho cx n * ttOf cx ht := by rw [h]

theorem fixed_imp (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁)
    (x : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (hA : ∀ d ∈ XS T M V₁ Mc y, d x = x) (htt : ttOf cx c.ht₁.1 x = x) :
    ∃ u : NZ T, (u : G) ∈ ZS153 T M V₁ ∧
      secMk (NZ T) (quasithinOmegaOneCenter T) u =
        (x : SecQuot (NZ T) (quasithinOmegaOneCenter T)) := by
  obtain ⟨u, huU, hux⟩ := mem_secImg.1 x.2
  let K₀ : Subgroup G :=
    ((MulAction.stabilizer (MulAut _) x).comap (rho cx)).map (NZ T).subtype
  have hX : Xgp153 T M V₁ Mc y ≤ K₀ := by
    intro n hn
    have hnN : n ∈ NZ T := Mc_le_NZ cx (X_le_Mc cx c.hy.1 c.h56.V0_eq hn)
    refine Subgroup.mem_map.2 ⟨⟨n, hnN⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    exact hA _ (rho_mem_XStar cx ⟨n, hnN⟩ hn)
  have ht : t₁ ∈ K₀ := by
    refine Subgroup.mem_map.2 ⟨⟨t₁, t₁_mem_NZ cx c.ht₁.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    exact htt
  have hK : Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁ ≤ K₀ :=
    sup_le hX (Subgroup.zpowers_le.2 ht)
  refine ⟨u, ?_, hux⟩
  rw [c.h56.fixed]
  refine ⟨huU, u.2, fun k hk => ?_⟩
  obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.1 (hK hk)
  have hrho : rho cx n x = x := by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hn
    exact hn
  have h1 := congrArg Subtype.val hrho
  rw [rho_apply_coe, ← hux] at h1
  have hcomm : secMk (NZ T) (quasithinOmegaOneCenter T) u * secMk (NZ T) (quasithinOmegaOneCenter T) n =
      secMk (NZ T) (quasithinOmegaOneCenter T) n * secMk (NZ T) (quasithinOmegaOneCenter T) u :=
    (mul_inv_eq_iff_eq_mul.1 h1).symm
  have := commutator_mem_of_secMk_commute (x := u) (y := n) hcomm
  have hnk' : (n : G) = k := hnk
  rw [← hnk']
  exact this

theorem exists_zS_aux (cx : Ctx15350 T Mc M V₁ V₂ t) : ∃ z ∈ ZS153 T M V₁,
    z ∉ quasithinOmegaOneCenter T := by
  by_contra h
  push Not at h
  have hle : ZS153 T M V₁ ≤ quasithinOmegaOneCenter T := h
  have := Subgroup.card_le_of_le hle
  rw [Decomp153.card_ZS cx.c.hyp cx.c.decomp, Z_card cx] at this
  omega

end Chain

end S153E57

end CFSG.Quasithin
