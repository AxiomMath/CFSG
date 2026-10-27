module

public import CFSG.Quasithin.EmptyFaithful.S143WFin
public import CFSG.Quasithin.EmptyFaithful.S143WNo
public import CFSG.Quasithin.EmptyFaithful.S142Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzPS8

section Generic

theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    A.relIndex (A ⊔ B) = A.relIndex B := by
  set N := Subgroup.normalizer (B : Set G) with hN
  have hBN : B ≤ N := Subgroup.le_normalizer
  have : (B.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h1 : (B.subgroupOf N).relIndex (A.subgroupOf N ⊔ B.subgroupOf N) =
      (B.subgroupOf N).relIndex (A.subgroupOf N) := Subgroup.relIndex_sup_right _ _
  rw [← Subgroup.subgroupOf_sup hAB hBN, Subgroup.relIndex_subgroupOf (sup_le hAB hBN),
    Subgroup.relIndex_subgroupOf hAB] at h1
  have c1 := Subgroup.relIndex_mul_relIndex (A ⊓ B) A (A ⊔ B) inf_le_left le_sup_left
  have c2 := Subgroup.relIndex_mul_relIndex (A ⊓ B) B (A ⊔ B) inf_le_right le_sup_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  rw [e1] at c1
  rw [e2, h1] at c2
  have hpos : B.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := c1.trans c2.symm
  rw [mul_comm (A.relIndex B)] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this

variable {H S : Type*} [Group H] [Group S]

theorem mem_of_map_mem [Finite H] (ρ : H →* S) {T P : Subgroup H} [P.Normal] (hT : IsPGroup 2 ↥T)
    (hTi : ¬ 2 ∣ T.index) (hker : ∀ k ∈ P, ρ k = 1 → k ∈ T) {p : H} (hp : p ∈ P)
    (hpT : ρ p ∈ T.map ρ) : p ∈ T := by
  set P₁ : Subgroup H := P ⊓ (T.map ρ).comap ρ with hP₁
  have hP₁p : IsPGroup 2 ↥P₁ := by
    intro x
    obtain ⟨t, htT, hρt⟩ := Subgroup.mem_map.mp x.2.2
    obtain ⟨a, ha⟩ := hT ⟨t, htT⟩
    have ht : t ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have h1 : ρ ((x : H) ^ 2 ^ a) = 1 := by
      rw [map_pow, ← hρt, ← map_pow, ht, map_one]
    have h2 : (x : H) ^ 2 ^ a ∈ T := hker _ (P.pow_mem x.2.1 _) h1
    obtain ⟨b, hb⟩ := hT ⟨_, h2⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simpa [pow_add, pow_mul] using this
  have hQ : T ⊓ P ≤ P₁ := fun x hx =>
    ⟨hx.2, Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem ρ hx.1)⟩
  have hP₁P : P₁ ≤ P := inf_le_left
  have hodd : ¬ 2 ∣ (T ⊓ P).relIndex P := by
    rw [Subgroup.inf_relIndex_right, ← relIndex_sup_of_le_normalizer
      (Subgroup.le_normalizer_of_normal : T ≤ Subgroup.normalizer (P : Set H))]
    exact fun hd => hTi (hd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ P) P₁ P hQ hP₁P
  have hodd' : ¬ 2 ∣ (T ⊓ P).relIndex P₁ := fun hd => hodd (hmul ▸ hd.mul_right _)
  obtain ⟨n, hn⟩ := hP₁p.index ((T ⊓ P).subgroupOf P₁)
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd' (by
      change 2 ∣ ((T ⊓ P).subgroupOf P₁).index
      rw [hn]
      exact dvd_pow_self 2 hne)
  have h1 : (T ⊓ P).relIndex P₁ = 1 := by
    change ((T ⊓ P).subgroupOf P₁).index = 1
    rw [hn, hn0, pow_zero]
  exact (Subgroup.relIndex_eq_one.mp h1 ⟨hp, Subgroup.mem_comap.mpr hpT⟩).1

theorem relIndex_eq_map (ρ : H →* S) {T₀ K : Subgroup H} (hTK : T₀ ≤ K)
    (hker : ∀ k ∈ K, ρ k = 1 → k ∈ T₀) :
    T₀.relIndex K = (T₀.map ρ).relIndex (K.map ρ) := by
  have h1 : ((T₀.map ρ).comap ρ).relIndex K = (T₀.map ρ).relIndex (K.map ρ) :=
    Subgroup.relIndex_comap (T₀.map ρ) ρ K
  rw [← h1]
  have h2 : ((T₀.map ρ).comap ρ) ⊓ K = T₀ := by
    apply le_antisymm
    · rintro x ⟨hx1, hx2⟩
      obtain ⟨t, htT, htx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx1)
      have : t⁻¹ * x ∈ T₀ := hker _ (K.mul_mem (K.inv_mem (hTK htT)) hx2) (by
        rw [map_mul, map_inv, htx, inv_mul_cancel])
      simpa using T₀.mul_mem htT this
    · intro x hx
      exact ⟨Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem ρ hx), hTK hx⟩
  conv_rhs => rw [← Subgroup.inf_relIndex_right, h2]

end Generic

section Hat

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem fix_of_overgroup_N (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T)
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    {P : Subgroup G} (hPH : P ≤ mcOf T) (hPn : ∀ x ∈ mcOf T, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hPT : P ⊓ Hyp1281Two.centralizerHat T M ≤ T)
    {J : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hJP : J ≤ D.img P)
    (hJn : ∀ t ∈ D.img T, ∀ j ∈ J, t * j * t⁻¹ ∈ J)
    (hidx : (D.img T).relIndex J = 3 ∨ (D.img T).relIndex J = 5) :
    ∀ α ∈ J, α (D.π a) = D.π a := by
  classical
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  set ρ := S143V.rhoH h D with hρ
  have hmapT : (T.subgroupOf (mcOf T)).map ρ = D.img T := S143V.map_rhoH h D hTH
  set T₀ : Subgroup ↥(mcOf T) := T.subgroupOf (mcOf T) with hT₀
  set P₀ : Subgroup ↥(mcOf T) := P.subgroupOf (mcOf T) with hP₀
  have hP₀n : P₀.Normal := ⟨fun n hn g => hPn (g : G) g.2 (n : G) hn⟩
  set K'₀ : Subgroup ↥(mcOf T) := P₀ ⊓ Subgroup.comap ρ J with hK'₀
  have hρT : ∀ t ∈ T₀, ρ t ∈ D.img T := fun t ht => hmapT ▸ Subgroup.mem_map_of_mem ρ ht
  have hnorm : ∀ t ∈ T₀, ∀ k ∈ K'₀, t * k * t⁻¹ ∈ K'₀ := by
    intro t ht k hk
    refine ⟨hPn (t : G) t.2 (k : G) hk.1, ?_⟩
    have h3 := hJn _ (hρT t ht) _ hk.2
    show ρ (t * k * t⁻¹) ∈ J
    rw [map_mul, map_mul, map_inv]
    exact h3
  have hmapK : K'₀.map ρ = J := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · intro n hn
      obtain ⟨x, hxP, hxN, hxρ⟩ := HatModel.mem_img.mp (hJP hn)
      have hxH : x ∈ mcOf T := hPH hxP
      refine ⟨⟨x, hxH⟩, ⟨hxP, ?_⟩, ?_⟩
      · show ρ ⟨x, hxH⟩ ∈ J
        rw [S143V.rhoH_apply h D _ hxN, hxρ]
        exact hn
      · rw [S143V.rhoH_apply h D _ hxN]
        exact hxρ
  have hT₀2 : IsPGroup 2 ↥T₀ := h.almostSpecialHyp_g1.sylow_H.2.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe h.almostSpecialHyp_g1.sylow_H.1).symm
  have hT₀i : ¬ 2 ∣ T₀.index := h.almostSpecialHyp_g1.sylow_H.2.2
  have hker : ∀ k ∈ P₀, ρ k = 1 → k ∈ T₀ := fun k hk hk1 =>
    hPT ⟨hk, (S143V.mem_ker_rhoH h D k).mp hk1⟩
  have hS : ∀ p ∈ P₀, ρ p ∈ T₀.map ρ → p ∈ T₀ := fun p hp hpT =>
    mem_of_map_mem ρ hT₀2 hT₀i hker hp hpT
  set K0 : Subgroup ↥(mcOf T) := T₀ ⊔ K'₀ with hK0
  have hTK : T₀ ≤ K0 := le_sup_left
  have hLE : T₀ ≤ Subgroup.normalizer (K'₀ : Set ↥(mcOf T)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hnorm t ht k hk, fun hk => ?_⟩
    have := hnorm t⁻¹ (T₀.inv_mem ht) _ hk
    simpa [mul_assoc] using this
  have hkerK : ∀ k ∈ K0, ρ k = 1 → k ∈ T₀ := by
    intro k hk hk1
    rw [← SetLike.mem_coe, hK0, Subgroup.coe_mul_of_left_le_normalizer_right T₀ K'₀ hLE] at hk
    obtain ⟨t, ht, k', hk', rfl⟩ := Set.mem_mul.mp hk
    have hρk' : ρ k' ∈ T₀.map ρ := by
      have : ρ k' = (ρ t)⁻¹ := by
        rw [map_mul] at hk1
        exact eq_inv_of_mul_eq_one_right hk1
      rw [this]
      exact (T₀.map ρ).inv_mem (Subgroup.mem_map_of_mem ρ ht)
    exact T₀.mul_mem ht (hS k' hk'.1 hρk')
  have hidx0 : T₀.relIndex K0 = (D.img T).relIndex J := by
    rw [relIndex_eq_map ρ hTK hkerK, hK0, Subgroup.map_sup, hmapT, hmapK]
    refine relIndex_sup_of_le_normalizer ?_
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => hJn t ht j hj, fun hj => ?_⟩
    have := hJn t⁻¹ ((D.img T).inv_mem ht) _ hj
    simpa [mul_assoc] using this
  set K : Subgroup G := K0.map (mcOf T).subtype with hK
  have hrelK : T.relIndex K = T₀.relIndex K0 := by
    have h1 := Subgroup.relIndex_map_map_of_injective T₀ K0 (mcOf T).subtype_injective
    rw [hT₀, Subgroup.map_subgroupOf_eq_of_le hTH] at h1
    exact h1
  have hTK' : T ≤ K := by
    intro t ht
    exact ⟨⟨t, hTH ht⟩, Subgroup.mem_sup_left (show (⟨t, hTH ht⟩ : ↥(mcOf T)) ∈ T₀ from ht), rfl⟩
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Hyp1281Two.omegaOneCenter_le_VZ T M).trans h.isTwoReducedIn.2
  have hKH : K ≤ mcOf T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hKnorm : K ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hKH.trans (Subgroup.centralizer_le_normalizer _)
  have hZp : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le hZT
  have hpc : quasithinOmegaOneCenter T ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 (hZT.trans hTK') hKnorm hZp
  have hinH : InH T K := ⟨hTK', fun hbot => h.omegaOneCenter_ne_bot
    (le_bot_iff.mp (hbot ▸ hpc))⟩
  have hKM : K ≤ M := h35 K hinH (by rw [hrelK, hidx0]; exact hidx)
  intro α hα
  rw [← hmapK] at hα
  obtain ⟨k, hk, rfl⟩ := hα
  have hkK : (k : G) ∈ K := ⟨k, Subgroup.mem_sup_right hk, rfl⟩
  exact S143V.rhoH_fix_of_mem_M h hU D haV haZ (hKM hkK)

end Hat

section Setting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def OvgFix (T0 N : Subgroup (V ≃ₗ[ZMod 2] V)) (v : V) : Prop :=
  ∀ J : Subgroup (V ≃ₗ[ZMod 2] V), J ≤ N → (∀ t ∈ T0, ∀ j ∈ J, t * j * t⁻¹ ∈ J) →
    (T0.relIndex J = 3 ∨ T0.relIndex J = 5) → ∀ α ∈ J, α v = v

structure OvgSetting (Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)) (v : V) : Prop where
  sylow : IsSylowTwoOf T0 Γ
  ne_zero : v ≠ 0
  fix : ∀ t ∈ T0, t v = v
  span_orbit : Submodule.span (ZMod 2) (MulAction.orbit Γ v) = ⊤
  exists_normal : ∃ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ Γ ∧
    (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) ∧ N ≠ ⊥ ∧ OvgFix T0 N v

structure OvgSymp (B : LinearMap.BilinForm (ZMod 2) V) (Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)) (v : V) :
    Prop extends OvgSetting Γ T0 v where
  alt : ∀ w, B w w = 0
  nondegenerate : ∀ w, (∀ x, B w x = 0) → w = 0
  isometry : ∀ γ ∈ Γ, ∀ w x, B (γ w) (γ x) = B w x

variable {Γ T0 N : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}

theorem OvgSetting.exists_normal_subtype (S : OvgSetting Γ T0 v) :
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N ≠ ⊥ ∧ OvgFix T0 (N.map Γ.subtype) v := by
  obtain ⟨N, hNΓ, hNn, hN1, hF⟩ := S.exists_normal
  refine ⟨N.subgroupOf Γ, ⟨fun n hn g => ?_⟩, ?_, ?_⟩
  · exact hNn (g : V ≃ₗ[ZMod 2] V) g.2 (n : V ≃ₗ[ZMod 2] V) hn
  · intro hbot
    apply hN1
    rw [← Subgroup.map_subgroupOf_eq_of_le hNΓ, hbot, Subgroup.map_bot]
  · rwa [Subgroup.map_subgroupOf_eq_of_le hNΓ]

theorem OvgSetting.false_of_fixes (S : OvgSetting Γ T0 v) (hNn : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hN1 : N ≠ ⊥) (hfix : ∀ α ∈ N, α v = v) : False := by
  have hall : ∀ n ∈ N, ∀ w : V, n w = w := by
    intro n hn
    have hsub : Submodule.span (ZMod 2) (MulAction.orbit Γ v) ≤
        LinearMap.ker (n.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hγn : (γ : V ≃ₗ[ZMod 2] V)⁻¹ * n * (γ : V ≃ₗ[ZMod 2] V) ∈ N := by
        have := hNn (γ : V ≃ₗ[ZMod 2] V)⁻¹ (Subgroup.inv_mem _ γ.2) n hn
        simpa [mul_assoc] using this
      have h2 : (γ : V ≃ₗ[ZMod 2] V)⁻¹ (n ((γ : V ≃ₗ[ZMod 2] V) v)) = v := hfix _ hγn
      show n ((γ : V ≃ₗ[ZMod 2] V) v) - (γ : V ≃ₗ[ZMod 2] V) v = 0
      have h3 : n ((γ : V ≃ₗ[ZMod 2] V) v) = (γ : V ≃ₗ[ZMod 2] V) v := by
        have := congrArg (fun w => (γ : V ≃ₗ[ZMod 2] V) w) h2
        simpa using this
      rw [h3, sub_self]
    intro w
    have hv : w ∈ LinearMap.ker (n.toLinearMap - LinearMap.id) := by
      apply hsub
      rw [S.span_orbit]
      exact Submodule.mem_top
    have := LinearMap.mem_ker.mp hv
    simpa [sub_eq_zero] using this
  apply hN1
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  ext w
  simpa using hall n hn w

theorem OvgFix.fix_of_subgroup (hT0 : T0 ≤ Γ) (hF : OvgFix T0 N v) (J : Subgroup ↥Γ)
    (hJN : J.map Γ.subtype ≤ N) (hJn : ∀ t ∈ T0.subgroupOf Γ, ∀ j ∈ J, t * j * t⁻¹ ∈ J)
    (hidx : (T0.subgroupOf Γ).relIndex J = 3 ∨ (T0.subgroupOf Γ).relIndex J = 5) :
    ∀ α ∈ J, (α : V ≃ₗ[ZMod 2] V) v = v := by
  have h1 := Subgroup.relIndex_map_map_of_injective (T0.subgroupOf Γ) J Γ.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hT0] at h1
  intro α hα
  refine hF (J.map Γ.subtype) hJN ?_ (by rw [h1]; exact hidx) α ⟨α, hα, rfl⟩
  rintro t ht _ ⟨j, hj, rfl⟩
  have ht' : t ∈ Γ := hT0 ht
  exact ⟨⟨t, ht'⟩ * j * ⟨t, ht'⟩⁻¹, hJn ⟨t, ht'⟩ ht j hj, by simp⟩

end Setting

section Sylow

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {Γ T0 T1 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}

theorem exists_conj_eq_of_isSylowTwoOf (h0 : IsSylowTwoOf T0 Γ) (h1 : IsSylowTwoOf T1 Γ) :
    ∃ g ∈ Γ, ∀ x : V ≃ₗ[ZMod 2] V, x ∈ T1 ↔ ∃ y ∈ T0, x = g * y * g⁻¹ := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P0 : Sylow 2 ↥Γ := IsPGroup.toSylow (P := T0.subgroupOf Γ)
    (h0.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h0.1).symm) h0.2.2
  let P1 : Sylow 2 ↥Γ := IsPGroup.toSylow (P := T1.subgroupOf Γ)
    (h1.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h1.1).symm) h1.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Γ P0 P1
  refine ⟨g, g.2, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have hxΓ : x ∈ Γ := h1.1 hx
    have hmem : (⟨x, hxΓ⟩ : ↥Γ) ∈ (P1 : Subgroup ↥Γ) := hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨b, hb, hbx⟩ := hmem
    refine ⟨(b : V ≃ₗ[ZMod 2] V), hb, ?_⟩
    have := congrArg Subtype.val hbx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this.symm
  · rintro ⟨y, hy, rfl⟩
    have hyΓ : y ∈ Γ := h0.1 hy
    have hmem : (⟨y, hyΓ⟩ : ↥Γ) ∈ (P0 : Subgroup ↥Γ) := hy
    have := Subgroup.smul_mem_pointwise_smul (⟨y, hyΓ⟩ : ↥Γ) (MulAut.conj g) (P0 : Subgroup ↥Γ) hmem
    rw [← Sylow.coe_subgroup_smul, hg] at this
    have h2 : MulAut.conj g • (⟨y, hyΓ⟩ : ↥Γ) = ⟨(g : V ≃ₗ[ZMod 2] V) * y * (g : V ≃ₗ[ZMod 2] V)⁻¹,
        Γ.mul_mem (Γ.mul_mem g.2 hyΓ) (Γ.inv_mem g.2)⟩ := by
      apply Subtype.ext
      simp [MulAut.smul_def, MulAut.conj_apply]
    rw [h2] at this
    exact this

theorem OvgSetting.exists_of_sylow (S : OvgSetting Γ T0 v) (hT1 : IsSylowTwoOf T1 Γ) :
    ∃ v' : V, OvgSetting Γ T1 v' := by
  classical
  obtain ⟨g, hgΓ, hg⟩ := exists_conj_eq_of_isSylowTwoOf S.sylow hT1
  obtain ⟨N, hNΓ, hNn, hN1, hF⟩ := S.exists_normal
  set c : (V ≃ₗ[ZMod 2] V) →* (V ≃ₗ[ZMod 2] V) := (MulAut.conj g).toMonoidHom with hc
  have hcx : ∀ x, c x = g * x * g⁻¹ := fun x => rfl
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hcsurj : Function.Surjective c := (MulAut.conj g).surjective
  have hT : T0.map c = T1 := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg _).mpr ⟨y, hy, hcx y⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (hg x).mp hx
      exact ⟨y, hy, hcx y⟩
  refine ⟨g v, hT1, ?_, ?_, ?_, ⟨N, hNΓ, hNn, hN1, ?_⟩⟩
  · intro h0
    exact S.ne_zero ((map_eq_zero_iff g g.injective).mp h0)
  · intro t ht
    obtain ⟨y, hy, rfl⟩ := (hg t).mp ht
    have := S.fix y hy
    simp [this]
  · have h2 : MulAction.orbit ↥Γ (g v) = MulAction.orbit ↥Γ v :=
      MulAction.orbit_smul (⟨g, hgΓ⟩ : ↥Γ) v
    rw [h2]
    exact S.span_orbit
  · intro J' hJ'N hJ'n hidx α' hα'
    set J : Subgroup (V ≃ₗ[ZMod 2] V) := J'.comap c with hJ
    have hJN : J ≤ N := by
      intro j hj
      have h2 := hNn g⁻¹ (Γ.inv_mem hgΓ) _ (hJ'N hj)
      rw [hcx] at h2
      simpa [mul_assoc] using h2
    have hJn : ∀ t ∈ T0, ∀ j ∈ J, t * j * t⁻¹ ∈ J := by
      intro t ht j hj
      show c (t * j * t⁻¹) ∈ J'
      rw [map_mul, map_mul, map_inv]
      exact hJ'n _ (hT ▸ Subgroup.mem_map_of_mem c ht) _ hj
    have hJmap : J.map c = J' := Subgroup.map_comap_eq_self_of_surjective hcsurj J'
    have hidxJ : T0.relIndex J = 3 ∨ T0.relIndex J = 5 := by
      have h1 := Subgroup.relIndex_map_map_of_injective T0 J hcinj
      rw [hT, hJmap] at h1
      rw [← h1]
      exact hidx
    have hα : (g⁻¹ * α' * g) ∈ J := by
      show c (g⁻¹ * α' * g) ∈ J'
      rw [hcx]
      simpa [mul_assoc] using hα'
    have h3 : (g⁻¹ * α' * g) v = v := hF J hJN hJn hidxJ _ hα
    have h4 : g ((g⁻¹ * α' * g) v) = g v := by rw [h3]
    simpa [mul_assoc] using h4

end Sylow

section Existence

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem ovgSetting_of_hyp (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T)
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M) :
    OvgSetting (D.img (mcOf T)) (D.img T) (D.π a) := by
  classical
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  set P : Subgroup G := mcOf T ⊓ Subgroup.centralizer (centerOf (uOfL22 T M) : Set G) with hP
  have hPH : P ≤ mcOf T := inf_le_left
  have hPZ : ∀ p ∈ P, ∀ z ∈ centerOf (uOfL22 T M), p * z = z * p := fun p hp z hz =>
    (Subgroup.mem_centralizer_iff.mp hp.2 z hz).symm
  have hPn : ∀ x ∈ mcOf T, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    refine ⟨(mcOf T).mul_mem ((mcOf T).mul_mem hx hp.1) ((mcOf T).inv_mem hx),
      Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hxN : x ∈ Subgroup.normalizer (centerOf (uOfL22 T M) : Set G) :=
      normalizer_le_normalizer_centerOf _ (h.g1_le_normalizer_uOfL22 hx)
    have hz' : x⁻¹ * z * x ∈ centerOf (uOfL22 T M) := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hxN) z).mp hz
      simpa using this
    have hc : p * (x⁻¹ * z * x) = (x⁻¹ * z * x) * p := hPZ p hp _ hz'
    calc z * (x * p * x⁻¹) = x * ((x⁻¹ * z * x) * p) * x⁻¹ := by group
      _ = x * (p * (x⁻¹ * z * x)) * x⁻¹ := by rw [hc]
      _ = (x * p * x⁻¹) * z := by group
  have hPT := S143W.inf_centralizerHat_le_T h hPH hPn hPZ
  have hΓne : D.img (mcOf T) ≠ ⊥ := by
    intro hbot
    have horb : ∀ w ∈ MulAction.orbit (D.img (mcOf T)) (D.π a), w = D.π a := by
      rintro w ⟨γ, rfl⟩
      have h1 : (γ : D.V ≃ₗ[ZMod 2] D.V) = 1 :=
        (Subgroup.eq_bot_iff_forall _).mp hbot _ γ.2
      show (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) = D.π a
      rw [h1]
      rfl
    obtain ⟨hπa, -, -⟩ := h.hat_VZ_cases hU D haV haZ
    obtain ⟨w, hw⟩ : ∃ w, D.B (D.π a) w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hπa (D.B_nondegenerate _ hcon)
    have hwtop : w ∈ Submodule.span (ZMod 2) (MulAction.orbit (D.img (mcOf T)) (D.π a)) := by
      rw [hyp.span_orbit]
      exact Submodule.mem_top
    have hle : Submodule.span (ZMod 2) (MulAction.orbit (D.img (mcOf T)) (D.π a)) ≤
        Submodule.span (ZMod 2) {D.π a} := by
      rw [Submodule.span_le]
      intro x hx
      rw [horb x hx]
      exact Submodule.subset_span rfl
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle hwtop)
    apply hw
    rw [map_smul, D.B_isAlt, smul_zero]
  have hN1 : D.img P ≠ ⊥ := by
    by_cases hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T
    · have hPH' : mcOf T ≤ P := fun x hx =>
        ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz => by
          rw [hZU] at hz
          exact Subgroup.mem_centralizer_iff.mp hx z hz⟩
      rw [le_antisymm hPH hPH']
      exact hΓne
    · have hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M) :=
        lt_of_le_of_ne h.omegaOneCenter_le_centerOf_uOfL22 (Ne.symm hZU)
      obtain ⟨y, hyX, hyH, hy1⟩ := S143W.exists_y₀ h hU hg D hlt
      have hyP : y ∈ P := ⟨hyH, Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (S143W.pOf_centralizes h hU hg (le_conjClosure _ _ hyX) hz).symm⟩
      have hyN : y ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hyH
      intro hbot
      have hmem : S143V.rhoH h D ⟨y, hyH⟩ ∈ D.img P := HatModel.mem_img.mpr ⟨y, hyP, hyN, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hy1 hmem
  have hNn : ∀ γ ∈ D.img (mcOf T), ∀ n ∈ D.img P, γ * n * γ⁻¹ ∈ D.img P := by
    intro γ hγ n hn
    obtain ⟨x, hxH, hxN, rfl⟩ := HatModel.mem_img.mp hγ
    obtain ⟨p, hpP, hpN, rfl⟩ := HatModel.mem_img.mp hn
    have hN : x * p * x⁻¹ ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
      (Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem
        ((Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem hxN hpN)
        ((Subgroup.normalizer (uOfL22 T M : Set G)).inv_mem hxN)
    refine HatModel.mem_img.mpr ⟨x * p * x⁻¹, hPn x hxH p hpP, hN, ?_⟩
    have e : (⟨x * p * x⁻¹, hN⟩ : ↥(Subgroup.normalizer (uOfL22 T M : Set G))) =
        ⟨x, hxN⟩ * ⟨p, hpN⟩ * ⟨x, hxN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  exact
    { sylow := S143V.isSylowTwoOf_img_T h D
      ne_zero := (h.hat_VZ_cases hU D haV haZ).1
      fix := fun t ht => MulAction.mem_stabilizer_iff.mp (h.img_T_le_stabilizer hU D haV haZ ht)
      span_orbit := hyp.span_orbit
      exists_normal := ⟨D.img P, HatModel.img_mono hPH, hNn, hN1,
        fun J hJ hJn hidx => fix_of_overgroup_N h hU D haV haZ h35 hPH hPn hPT hJ hJn hidx⟩ }

theorem ovgSymp_of_hyp (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T)
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M) :
    OvgSymp D.B (D.img (mcOf T)) (D.img T) (D.π a) := by
  obtain ⟨g, hg⟩ := h.exists_goodElt_L
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  exact { ovgSetting_of_hyp h hU D haV haZ h35 with
    alt := hyp.alt
    nondegenerate := hyp.nondegenerate
    isometry := hyp.isometry }

theorem exists_ovgSetting (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) : ∃ v : D.V, OvgSetting (D.img (mcOf T)) (D.img T) v := by
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  exact ⟨D.π a, ovgSetting_of_hyp h1281 hU D haV haZ
    (fun K hK hidx => h35 G T M hyp hnot K hK hidx)⟩

theorem exists_ovgSymp (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) : ∃ v : D.V, OvgSymp D.B (D.img (mcOf T)) (D.img T) v := by
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  exact ⟨D.π a, ovgSymp_of_hyp h1281 hU D haV haZ
    (fun K hK hidx => h35 G T M hyp hnot K hK hidx)⟩

end Existence

end SzPS8

end CFSG.Quasithin
