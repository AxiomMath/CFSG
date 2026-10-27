module

public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Local

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152J2

open Subgroup

theorem factorization_two_604800 : (604800 : ℕ).factorization 2 = 7 := by
  rw [show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_three_604800 : (604800 : ℕ).factorization 3 = 3 := by
  rw [show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem core_of_perm {Gp : Type*} [Group Gp] [Finite Gp] {X : Subgroup Gp}
    (hX : Nat.card X = 604800) {Tp Wp Sp : Subgroup Gp} {z0 y0 : Gp} (hT : Tp ≤ X)
    (hTc : Nat.card Tp = 128) (hW : Wp ≤ X)
    (hWT : Wp ≤ Subgroup.closure ((fun x : Gp => x ^ 2) '' (Tp : Set Gp))) (hS : Sp ≤ X)
    (hSc : Nat.card Sp = 27) (hz1 : z0 ≠ 1) (hzS : z0 ∈ Sp)
    (hSz : Sp ≤ Subgroup.centralizer ({z0} : Set Gp)) (hy : y0 ∈ X) (hy5 : y0 ^ 5 = 1)
    (hy1 : y0 ≠ 1) (hzy : z0 * y0 = y0 * z0)
    (hcore : ∀ g ∈ X, X ≤ Wp ⊔ Subgroup.zpowers (g * y0 * g⁻¹)) :
    ∃ (T : Sylow 2 X) (W : Subgroup X) (S₀ : Sylow 3 X) (z₀ y₀ : X),
      W ≤ Subgroup.closure ((fun x : X => x ^ 2) '' ((T : Subgroup X) : Set X)) ∧ z₀ ≠ 1 ∧
      z₀ ∈ (S₀ : Subgroup X) ∧ (S₀ : Subgroup X) ≤ Subgroup.centralizer ({z₀} : Set X) ∧
      orderOf y₀ = 5 ∧ z₀ * y₀ = y₀ * z₀ ∧
      ∀ g : X, W ⊔ Subgroup.zpowers (g * y₀ * g⁻¹) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hTcard : Nat.card (Tp.subgroupOf X) = 2 ^ (Nat.card X).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv, hTc, hX,
      factorization_two_604800]
    norm_num
  have hScard : Nat.card (Sp.subgroupOf X) = 3 ^ (Nat.card X).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, hSc, hX,
      factorization_three_604800]
    norm_num
  have hTcoe : ((Sylow.ofCard (Tp.subgroupOf X) hTcard : Sylow 2 X) : Subgroup X) =
      Tp.subgroupOf X := rfl
  have hScoe : ((Sylow.ofCard (Sp.subgroupOf X) hScard : Sylow 3 X) : Subgroup X) =
      Sp.subgroupOf X := rfl
  refine ⟨Sylow.ofCard (Tp.subgroupOf X) hTcard, Wp.subgroupOf X,
    Sylow.ofCard (Sp.subgroupOf X) hScard, ⟨z0, hS hzS⟩, ⟨y0, hy⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    set C := Subgroup.closure ((fun x : X => x ^ 2) '' (((Sylow.ofCard (Tp.subgroupOf X) hTcard :
      Sylow 2 X) : Subgroup X) : Set X)) with hC
    have hle : Wp ≤ C.map X.subtype := by
      refine hWT.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x, hT hx⟩ ^ 2, Subgroup.subset_closure ⟨⟨x, hT hx⟩, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, hTcoe]
        exact Subgroup.mem_subgroupOf.mpr hx
      · rfl
    intro w hw
    obtain ⟨c, hc, hcw⟩ := hle (Subgroup.mem_subgroupOf.mp hw)
    exact (Subtype.ext hcw : c = w) ▸ hc
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · rw [hScoe]
    exact Subgroup.mem_subgroupOf.mpr hzS
  · rw [hScoe]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : t = ⟨z0, hS hzS⟩ := ht
    subst ht'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hSz (Subgroup.mem_subgroupOf.mp hs)) z0
      rfl)
  · exact orderOf_eq_prime (Subtype.ext hy5) (fun h => hy1 (congrArg Subtype.val h))
  · exact Subtype.ext hzy
  · intro g
    refine eq_top_iff.mpr fun x _ => ?_
    have hmap : (Wp.subgroupOf X ⊔ Subgroup.zpowers (g * (⟨y0, hy⟩ : X) * g⁻¹)).map X.subtype =
        Wp ⊔ Subgroup.zpowers (g.1 * y0 * g.1⁻¹) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hW]
      rfl
    have hx := hcore g.1 g.2 x.2
    rw [← hmap] at hx
    obtain ⟨c, hc, hcx⟩ := hx
    exact (Subtype.ext hcx : c = x) ▸ hc

@[expose] def GenStmt (Γ : Type) [Group Γ] : Prop :=
  ∀ z : Γ, z ≠ 1 →
    (∃ S : Sylow 3 Γ, z ∈ (S : Subgroup Γ) ∧
      (S : Subgroup Γ) ≤ Subgroup.centralizer ({z} : Set Γ)) →
    ∀ Q F : Subgroup Γ, IsPGroup 2 Q → 64 ∣ Nat.card Q → F ≤ Subgroup.centralizer ({z} : Set Γ) →
      Group.IsPerfect F → Nat.card F = 60 → Q ⊔ F = ⊤

theorem genStmt_of_core
    {G : Type} [Group G] [Finite G]
    (hG : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)) (T : Sylow 2 G) (W : Subgroup G)
    (hW : W ≤ Subgroup.closure ((fun x : G => x ^ 2) '' ((T : Subgroup G) : Set G)))
    (S₀ : Sylow 3 G) {z₀ : G} (hz₀ : z₀ ≠ 1) (hz₀S : z₀ ∈ (S₀ : Subgroup G))
    (hS₀ : (S₀ : Subgroup G) ≤ Subgroup.centralizer ({z₀} : Set G))
    {y₀ : G} (hy₀ : orderOf y₀ = 5) (hy₀z : z₀ * y₀ = y₀ * z₀)
    (hcore : ∀ g : G, W ⊔ Subgroup.zpowers (g * y₀ * g⁻¹) = ⊤) : GenStmt G := by
  intro z hz ⟨S, hzS, hS⟩ Q F hQ h64 hF _ hF60
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (show 5 ∣ Nat.card F by rw [hF60]; norm_num)
  have hyz : z * (y : G) = (y : G) * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hF y.2)).symm
  have hy5 : orderOf (y : G) = 5 := by rw [← hy, Subgroup.orderOf_coe]
  have := gen_of_core hG T W hW S₀ hz₀ hz₀S hS₀ hy₀ hy₀z hcore S hy5 hz hzS hS hyz hQ h64
  refine eq_top_iff.mpr ?_
  rw [← this]
  exact sup_le_sup_left (Subgroup.zpowers_le.mpr y.2) Q

theorem genStmt_of_equiv {Γ G : Type} [Group Γ] [Finite Γ] [Group G] (φ : Γ ≃* G)
    (h : GenStmt G) : GenStmt Γ := by
  intro z hz ⟨S, hzS, hS⟩ Q F hQ h64 hF hFp hF60
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := φ.injective
  have hz' : φ z ≠ 1 := fun h1 => hz (φ.injective (by rw [h1, map_one]))
  have hSmap : (S.mapSurjective (f := φ.toMonoidHom) φ.surjective : Subgroup G) =
      S.map φ.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hS' : ∃ S' : Sylow 3 G, φ z ∈ (S' : Subgroup G) ∧
      (S' : Subgroup G) ≤ Subgroup.centralizer ({φ z} : Set G) := by
    refine ⟨S.mapSurjective (f := φ.toMonoidHom) φ.surjective, ?_, ?_⟩
    · rw [hSmap]
      exact Subgroup.mem_map_of_mem _ hzS
    · rw [hSmap]
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
      change φ s * φ z = φ z * φ s
      rw [← map_mul, ← map_mul, this]
  have hF' : F.map φ.toMonoidHom ≤ Subgroup.centralizer ({φ z} : Set G) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hF hf)
    change φ f * φ z = φ z * φ f
    rw [← map_mul, ← map_mul, this]
  have hFp' : Group.IsPerfect (F.map φ.toMonoidHom) := by
    have := hFp
    exact Group.IsPerfect.map φ.toMonoidHom
  have key := h (φ z) hz' hS' (Q.map φ.toMonoidHom) (F.map φ.toMonoidHom) (hQ.map φ.toMonoidHom)
    (by rwa [Subgroup.card_map_of_injective hinj]) hF' hFp'
    (by rwa [Subgroup.card_map_of_injective hinj])
  rw [← Subgroup.map_sup] at key
  have := congrArg (Subgroup.comap φ.toMonoidHom) key
  rwa [Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.comap_top] at this

end CFSG.RankThree.PartTwo.KFacts.KS152J2
