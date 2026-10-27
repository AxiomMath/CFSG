module

public import CFSG.Quasithin.EmptyFaithful.S143WFin
public import CFSG.Quasithin.EmptyFaithful.SzN28S8Mod
public import CFSG.Quasithin.EmptyFaithful.SzN28Split
public import CFSG.Quasithin.EmptyFaithful.S143VSq
public import CFSG.Quasithin.EmptyFaithful.S143WNo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11 CFSG.Quasithin.S143W
open scoped commutatorElement

namespace SzN28

theorem add_self_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : v + v = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) v, h2, zero_smul]

theorem exists_selfDual_equiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : ∀ v, (∀ w, B v w = 0) → v = 0) :
    ∃ Φ : Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] V, ∀ μ w, B (Φ μ) w = μ w := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hB v fun w => by rw [hv]; rfl
  have hbij : Function.Bijective B := by
    refine ⟨hinj, ?_⟩
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)) (Subspace.dual_finrank_eq (K := ZMod 2) (V := V)).symm).1 hinj
    exact this
  refine ⟨(LinearEquiv.ofBijective (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) hbij).symm, fun μ w => ?_⟩
  have := LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) hbij) μ
  have h2 := congrArg (fun f : Module.Dual (ZMod 2) V => f w) this
  exact h2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section Main

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T (yOfL22 T M) g) (D : HatModel T M)

include h hU hg in
theorem false_of_lt_s8
    (hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M))
    (h8 : G112Concl8S8 D.B (D.img (mcOf T)) (D.img (rconj (Hyp1281Two.wOfU T M) g))) : False := by
  classical
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  obtain ⟨Tm⟩ := exists_tildeModel h
  obtain ⟨z, hzZ, hz1, hzz, hall⟩ := S143V.exists_zgen_sq h
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have h101 := hyp.toG101Hyp
  have hPH := pOf_le_H h hU hg
  have hPn : ∀ x ∈ mcOf T, ∀ p ∈ pOf T M g, x * p * x⁻¹ ∈ pOf T M g :=
    fun x hx p hp => pOf_normalized x hx hp
  have hPZ : ∀ p ∈ pOf T M g, ∀ z ∈ centerOf (uOfL22 T M), p * z = z * p :=
    fun p hp z hz => pOf_centralizes h hU hg hp hz
  have hPQ := inf_centralizerHat_le_pCore h hPH hPn hPZ
  set Γ : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := D.img (mcOf T) with hΓ
  set Pd : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := D.img (pOf T M g) with hPd
  have hPdΓ : Pd ≤ Γ := HatModel.img_mono hPH
  have hPdn : ∀ γ ∈ Γ, ∀ n ∈ Pd, γ * n * γ⁻¹ ∈ Pd := by
    intro γ hγ n hn
    obtain ⟨x, hxH, hxN, rfl⟩ := HatModel.mem_img.mp hγ
    obtain ⟨p, hpP, hpN, rfl⟩ := HatModel.mem_img.mp hn
    have hN : x * p * x⁻¹ ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
      (Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem
        ((Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem hxN hpN)
        ((Subgroup.normalizer (uOfL22 T M : Set G)).inv_mem hxN)
    refine HatModel.mem_img.mpr ⟨x * p * x⁻¹, pOf_normalized x hxH hpP, hN, ?_⟩
    have e : (⟨x * p * x⁻¹, hN⟩ : ↥(Subgroup.normalizer (uOfL22 T M : Set G))) =
        ⟨x, hxN⟩ * ⟨p, hpN⟩ * ⟨x, hxN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  obtain ⟨y₀, hy₀X, hy₀H, hy₀1⟩ := exists_y₀ h hU hg D hlt
  have hy₀P : y₀ ∈ pOf T M g := le_conjClosure _ _ hy₀X
  have hy₀N : y₀ ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hy₀H
  have hPd1 : Pd ≠ ⊥ := by
    intro hbot
    have hmem : S143V.rhoH h D ⟨y₀, hy₀H⟩ ∈ Pd := HatModel.mem_img.mpr ⟨y₀, hy₀P, hy₀N, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy₀1 hmem
  obtain ⟨A, I, I', x, hS8⟩ := s8Data_of_concl8 h101.X_le h101.X_sq h8
  have hAPd : A ≤ Pd := hS8.A_min Pd hPdΓ hPdn hPd1
  have t := hS8.twoNat
  have hv0 : D.π a ≠ 0 := (h.hat_VZ_cases hU D haV haZ).1
  have hperp : ∀ γ ∈ D.img (mcOf T), (∀ x : D.V, D.B x (D.π a) = 0 → γ x = x) → γ = 1 := by
    intro γ hγ hfix
    by_contra hγ1
    obtain ⟨a₁, b₁, h1, h2, h3⟩ := hS8.exists_three γ hγ hγ1
    have hB1 : D.B a₁ (D.π a) ≠ 0 := fun hz => h1 (hfix a₁ hz)
    have hB2 : D.B b₁ (D.π a) ≠ 0 := fun hz => h2 (hfix b₁ hz)
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    have hB3 : D.B (a₁ + b₁) (D.π a) = 0 := by
      rw [map_add, LinearMap.add_apply, key _ hB1, key _ hB2]
      decide
    have h4 := hfix _ hB3
    rw [map_add] at h4
    apply h3
    have huw : (γ a₁ - a₁) + (γ b₁ - b₁) = 0 := by
      calc (γ a₁ - a₁) + (γ b₁ - b₁) = (γ a₁ + γ b₁) - (a₁ + b₁) := by abel
        _ = 0 := by rw [h4]; exact sub_self _
    exact (eq_neg_of_add_eq_zero_left huw).trans (neg_eq_of_add_eq_zero_right (add_self_zmod_two _))
  obtain ⟨y, hyH, hyX, w, hzgU, hcom⟩ :=
    exists_commutator_vec h hU hg D Tm haV haZ hperp hlt hzZ hz1 hzz hall
  set rh := S143V.rhoH h D with hrh
  set K : Subgroup ↥(mcOf T) :=
    (pOf T M g).subgroupOf (mcOf T) ⊓ Subgroup.comap rh A with hK
  have hrange : rh.range = Γ := S143V.range_rhoH h D
  have hrhΓ : ∀ k : ↥(mcOf T), rh k ∈ Γ := fun k => by
    rw [← hrange]
    exact ⟨k, rfl⟩
  have hKn : K.Normal := by
    refine ⟨fun k hk x => ⟨hPn (x : G) x.2 (k : G) hk.1, ?_⟩⟩
    have h2 : rh k ∈ A := hk.2
    have h3 := hS8.A_normal _ (hrhΓ x) _ h2
    show rh (x * k * x⁻¹) ∈ A
    rw [map_mul, map_mul, map_inv]
    exact h3
  have hKmap : K.map rh = A := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · intro n hn
      obtain ⟨x', hxP, hxN, hxρ⟩ := HatModel.mem_img.mp (hAPd hn)
      have hxH : x' ∈ mcOf T := hPH hxP
      refine ⟨⟨x', hxH⟩, ⟨hxP, ?_⟩, ?_⟩
      · show rh ⟨x', hxH⟩ ∈ A
        rw [S143V.rhoH_apply h D _ hxN, hxρ]
        exact hn
      · rw [S143V.rhoH_apply h D _ hxN]
        exact hxρ
  have hker : ∀ k ∈ K, rh k = 1 → Tm.ρ k = 1 := by
    intro k hk hk1
    have hkR : (k : G) ∈ Hyp1281Two.centralizerHat T M := (S143V.mem_ker_rhoH h D k).mp hk1
    exact tilde_rho_eq_one_of_mem_pCore h Tm k (hPQ ⟨hk.1, hkR⟩)
  have hKZ : ∀ k ∈ K, ∀ z' : Tm.V, Tm.phi h D z' = 0 → Tm.ρ k z' = z' := by
    intro k hk z' hz'
    obtain ⟨u, huC, rfl⟩ := (Tm.phi_eq_zero_iff h D z').mp hz'
    have hku : (k : G) * (u : G) * (k : G)⁻¹ ∈ uOfL22 T M :=
      HatModel.conj_mem_uOfL22 (h.g1_le_normalizer_uOfL22 k.2) u.2
    rw [Tm.ρ_c k u hku]
    congr 1
    apply Subtype.ext
    show (k : G) * (u : G) * (k : G)⁻¹ = (u : G)
    have hc : (k : G) * (u : G) = (u : G) * (k : G) := pOf_centralizes h hU hg hk.1 huC
    calc (k : G) * (u : G) * (k : G)⁻¹ = ((u : G) * (k : G)) * (k : G)⁻¹ := by rw [hc]
      _ = (u : G) := by group
  set Y : Subgroup ↥(mcOf T) := (rconj (centerOf (uOfL22 T M)) g).subgroupOf (mcOf T) with hY
  have hYZ : ∀ y' ∈ Y, ∀ z' : Tm.V, Tm.phi h D z' = 0 → Tm.ρ y' z' = z' := by
    intro y' hy' z' hz'
    obtain ⟨u, huC, rfl⟩ := (Tm.phi_eq_zero_iff h D z').mp hz'
    have hku : (y' : G) * (u : G) * (y' : G)⁻¹ ∈ uOfL22 T M :=
      HatModel.conj_mem_uOfL22 (h.g1_le_normalizer_uOfL22 y'.2) u.2
    rw [Tm.ρ_c y' u hku]
    congr 1
    apply Subtype.ext
    show (y' : G) * (u : G) * (y' : G)⁻¹ = (u : G)
    have hcomm : ⁅(u : G), (y' : G)⁆ = 1 := by
      have : ⁅(u : G), (y' : G)⁆ ∈ ⁅centerOf (uOfL22 T M), rconj (centerOf (uOfL22 T M)) g⁆ :=
        Subgroup.commutator_mem_commutator huC hy'
      rw [(h.lemma_12_8_13_three hU hg).2.2] at this
      exact Subgroup.mem_bot.mp this
    have hc : (y' : G) * (u : G) = (u : G) * (y' : G) := by
      calc (y' : G) * (u : G) = ((u : G) * (y' : G) * (u : G)⁻¹ * (y' : G)⁻¹)⁻¹ * ((u : G) * (y' : G)) := by
            group
        _ = (u : G) * (y' : G) := by
            rw [show (u : G) * (y' : G) * (u : G)⁻¹ * (y' : G)⁻¹ = ⁅(u : G), (y' : G)⁆ from
              (commutatorElement_def _ _).symm, hcomm]
            group
    calc (y' : G) * (u : G) * (y' : G)⁻¹ = ((u : G) * (y' : G)) * (y' : G)⁻¹ := by rw [hc]
      _ = (u : G) := by group
  have hv : Tm.c ⟨g⁻¹ * z * g, hzgU⟩ ∈ Submodule.span (ZMod 2)
      {x : Tm.V | ∃ y' ∈ Y, ∃ w' : Tm.V, x = Tm.ρ y' w' - w'} :=
    Submodule.subset_span ⟨⟨y, hyH⟩, hyX, Tm.c w, hcom.symm⟩
  have hV : ∀ w' ∈ VZ T M, ∃ hw : w' ∈ uOfL22 T M,
      Tm.c ⟨w', hw⟩ = 0 ∨ Tm.c ⟨w', hw⟩ = Tm.c ⟨g⁻¹ * z * g, hzgU⟩ := by
    intro w' hw'
    have hw'U : w' ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hw'
    refine ⟨hw'U, ?_⟩
    obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul_of_mem_VZ hU hg hw'
    have ha'U : a' ∈ uOfL22 T M :=
      Hyp1281Two.VZ_le_uOfL22 T M (Hyp1281Two.omegaOneCenter_le_VZ T M ha')
    have hb'U : b' ∈ uOfL22 T M := by
      have : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M :=
        (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
      exact Hyp1281Two.VZ_le_uOfL22 T M (this hb')
    have e : (⟨a' * b', hw'U⟩ : ↥(uOfL22 T M)) = ⟨a', ha'U⟩ * ⟨b', hb'U⟩ := rfl
    have hca : Tm.c ⟨a', ha'U⟩ = 0 := (Tm.c_eq_zero_iff _).mpr ha'
    rw [e, Tm.c_mul, hca, zero_add]
    rcases hall _ (mem_rconj.mp hb') with h0 | h0
    · left
      have : b' = 1 := by
        calc b' = g⁻¹ * (g * b' * g⁻¹) * g := by group
          _ = 1 := by rw [h0]; group
      have e2 : (⟨b', hb'U⟩ : ↥(uOfL22 T M)) = 1 := Subtype.ext this
      rw [e2, Tm.c_one]
    · right
      have : b' = g⁻¹ * z * g := by
        calc b' = g⁻¹ * (g * b' * g⁻¹) * g := by group
          _ = g⁻¹ * z * g := by rw [h0]
      have e2 : (⟨b', hb'U⟩ : ↥(uOfL22 T M)) = ⟨g⁻¹ * z * g, hzgU⟩ := Subtype.ext this
      rw [e2]
  have hgen := span_orbit_eq_top h Tm (Tm.c ⟨g⁻¹ * z * g, hzgU⟩) hV
  obtain ⟨Φ, hΦ⟩ := exists_selfDual_equiv D.B h101.nondegenerate
  let ρK : ↥K →* (Tm.V ≃ₗ[ZMod 2] Tm.V) := Tm.ρ.comp K.subtype
  let σK : ↥K →* (D.V ≃ₗ[ZMod 2] D.V) := rh.comp K.subtype
  have hσA : ∀ k : ↥K, σK k ∈ A := fun k => k.2.2
  have hsA : ∀ a' ∈ A, ∃ k : ↥K, σK k = a' := by
    intro a' ha'
    have : a' ∈ K.map rh := by rw [hKmap]; exact ha'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 this
    exact ⟨⟨k, hk⟩, rfl⟩
  have hΦkey : ∀ (ν : Module.Dual (ZMod 2) D.V) (v : D.V), (∀ w, D.B v w = ν w) → Φ ν = v := by
    intro ν v hv
    have h0 := h101.nondegenerate (Φ ν - v) (fun w => by
      rw [map_sub, LinearMap.sub_apply, hΦ, hv w, sub_self])
    exact sub_eq_zero.1 h0
  have hΦeq : ∀ (k : ↥K) (μ : Module.Dual (ZMod 2) D.V),
      Φ (μ ∘ₗ ((σK k⁻¹ : D.V ≃ₗ[ZMod 2] D.V) : D.V →ₗ[ZMod 2] D.V)) = σK k (Φ μ) := by
    intro k μ
    apply hΦkey
    intro w
    have hσk : σK k ∈ Γ := hrhΓ k
    have h1 := h101.isometry (σK k) hσk (Φ μ) (σK k⁻¹ w)
    have h2 : σK k (σK k⁻¹ w) = w := by
      have := congrArg (fun f : D.V ≃ₗ[ZMod 2] D.V => f w) (mul_inv_cancel (σK k))
      rw [map_inv]
      exact this
    rw [h2] at h1
    rw [h1, hΦ]
    rfl
  have hsplit := split_of_dual ρK σK (Tm.phi h D) (Tm.phi_surjective h D)
    (fun k x => Tm.phi_ρ h D (k : ↥(mcOf T)) x)
    (fun k z hz => hKZ k k.2 z hz) (fun k hk => hker k k.2 hk) Φ hΦeq
    (fun u hu => t.fix_eq_zero u fun a' ha' => by
      obtain ⟨k, hk⟩ := hsA a' ha'
      rw [← hk]
      exact hu k)
    (fun δ hδ hδker => t.coh σK hσA hsA δ hδ hδker)
  have hker0 := ker_eq_bot_of_decomp Tm.ρ (Tm.phi h D) K hKn hsplit.1 hsplit.2 Y hYZ _ hv hgen
  obtain ⟨-, u, huC, huN⟩ := IsConcreteLE.lt_iff_le_and_exists.mp hlt
  have huU : u ∈ uOfL22 T M := huC.1
  have hu0 : Tm.phi h D (Tm.c ⟨u, huU⟩) = 0 := by
    rw [Tm.phi_c h D, D.π_eq_zero_iff huU]
    exact huC
  exact huN ((Tm.c_eq_zero_iff _).mp (hker0 _ hu0))

end Main

end SzN28


end CFSG.Quasithin
