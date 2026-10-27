module

public import CFSG.Quasithin.EmptyFaithful.S143VBr
public import CFSG.Quasithin.EmptyFaithful.S143VGen
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTwelveD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M)
  {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T)

include h hU haV haZ

theorem rhoH_fix_of_mem_M {x : ↥(mcOf T)} (hxM : (x : G) ∈ M) :
    rhoH h D x (D.π a) = D.π a := by
  obtain ⟨hπa, hπV, hcases⟩ := h.hat_VZ_cases hU D haV haZ
  have hxN : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    h.g1_le_normalizer_uOfL22 x.2
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M haV
  have hxa : (x : G) * a * (x : G)⁻¹ ∈ VZ T M :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ M hxM) a).mp haV
  have hmem : D.π ((x : G) * a * (x : G)⁻¹) ∈ D.hat (VZ T M) :=
    D.π_mem_hat hxa (Hyp1281Two.VZ_le_uOfL22 T M hxa)
  rw [rhoH_apply h D x hxN, D.rho_π ⟨x, hxN⟩ haU]
  rcases hcases _ hmem with h0 | h0
  · exfalso
    apply hπa
    have h1 := D.rho_π ⟨x, hxN⟩ haU
    have h2 : D.rho ⟨x, hxN⟩ (D.π a) = 0 := by rw [h1]; exact h0
    exact (map_eq_zero_iff _ (D.rho ⟨x, hxN⟩).injective).mp h2
  · exact h0

end

section Main

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
  (haZ : a ∉ quasithinOmegaOneCenter T)

include h hU hg haV haZ

theorem no_normal_three_five
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (hker : Hyp1281Two.centralizerHat T M ≤ T)
    {N : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hNΓ : N ≤ D.img (mcOf T))
    (hNn : ∀ γ ∈ D.img (mcOf T), ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hN : Nat.card N = 3 ∨ Nat.card N = 5) : False := by
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hrange : (rhoH h D).range = D.img (mcOf T) := range_rhoH h D
  have hker' : (rhoH h D).ker ≤ T.subgroupOf (mcOf T) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hker ((mem_ker_rhoH h D x).mp hx))
  have hmapT : (T.subgroupOf (mcOf T)).map (rhoH h D) = D.img T := map_rhoH h D hTH
  have hP2 : IsPGroup 2 ↥(D.img T) := (isSylowTwoOf_img_T h D).2.1
  have hNT : ∀ x ∈ N, x ∈ D.img T → x = 1 := by
    intro x hxN hxT
    have h1 : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP2 (⟨x, hxT⟩ : D.img T)
    rw [Subgroup.orderOf_mk] at hk
    rcases hN with hN | hN
    · rw [hN] at h1
      rcases (Nat.dvd_prime (by norm_num)).mp h1 with h2 | h2
      · exact orderOf_eq_one_iff.mp h2
      · rw [h2] at hk
        rcases k with _ | k
        · simp at hk
        · rw [pow_succ] at hk
          omega
    · rw [hN] at h1
      rcases (Nat.dvd_prime (by norm_num)).mp h1 with h2 | h2
      · exact orderOf_eq_one_iff.mp h2
      · rw [h2] at hk
        rcases k with _ | k
        · simp at hk
        · rw [pow_succ] at hk
          omega
  have hNr : N ≤ (rhoH h D).range := hrange ▸ hNΓ
  have hNn' : ∀ s ∈ (rhoH h D).range, ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    rw [hrange]
    exact hNn
  have hidx := relIndex_comap_sup_map (rhoH h D) hker' hNr hNn' (by rw [hmapT]; exact hNT)
  rw [hmapT] at hidx
  set K0 : Subgroup ↥(mcOf T) := Subgroup.comap (rhoH h D) (N ⊔ D.img T) with hK0
  set K : Subgroup G := K0.map (mcOf T).subtype with hK
  have hrelK : T.relIndex K = Nat.card N := by
    have h1 := Subgroup.relIndex_map_map_of_injective (T.subgroupOf (mcOf T)) K0
      (mcOf T).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTH] at h1
    rw [h1]
    exact hidx
  have hTK : T ≤ K := by
    intro t ht
    refine ⟨⟨t, hTH ht⟩, ?_, rfl⟩
    have hxN : t ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 (hTH ht)
    have : rhoH h D ⟨t, hTH ht⟩ ∈ D.img T := by
      rw [rhoH_apply h D _ hxN]
      exact HatModel.rho_mem_img ht hxN
    exact Subgroup.mem_sup_right this
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Hyp1281Two.omegaOneCenter_le_VZ T M).trans h.isTwoReducedIn.2
  have hKH : K ≤ mcOf T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hKnorm : K ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hKH.trans (Subgroup.centralizer_le_normalizer _)
  have hZp : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le hZT
  have hpc : quasithinOmegaOneCenter T ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 (hZT.trans hTK) hKnorm hZp
  have hinH : InH T K := ⟨hTK, fun hbot => h.omegaOneCenter_ne_bot
    (le_bot_iff.mp (hbot ▸ hpc))⟩
  have hKM : K ≤ M := h35 K hinH (by rw [hrelK]; exact hN)
  have hfix : ∀ n ∈ N, n (D.π a) = D.π a := by
    intro n hn
    obtain ⟨x, hxK0, hxn⟩ := exists_mem_comap_of_mem (rhoH h D) (hNr hn)
      (show n ∈ N ⊔ D.img T from Subgroup.mem_sup_left hn)
    have hxM : (x : G) ∈ M := hKM ⟨x, hxK0, rfl⟩
    rw [← hxn]
    exact rhoH_fix_of_mem_M h hU D haV haZ hxM
  have hall : ∀ n ∈ N, ∀ v : D.V, n v = v := by
    intro n hn
    have hsub : Submodule.span (ZMod 2) (MulAction.orbit (D.img (mcOf T)) (D.π a)) ≤
        LinearMap.ker (n.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hγn : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ * n * (γ : D.V ≃ₗ[ZMod 2] D.V) ∈ N := by
        have := hNn (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ (Subgroup.inv_mem _ γ.2) n hn
        simpa [mul_assoc] using this
      have h1 := hfix _ hγn
      have h2 : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ (n ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a))) = D.π a := h1
      show n ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a)) - (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) = 0
      have h3 : n ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a)) = (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
        have := congrArg (fun w => (γ : D.V ≃ₗ[ZMod 2] D.V) w) h2
        simpa using this
      rw [h3, sub_self]
    intro v
    have hv : v ∈ LinearMap.ker (n.toLinearMap - LinearMap.id) := by
      apply hsub
      rw [hyp.span_orbit]
      exact Submodule.mem_top
    have := LinearMap.mem_ker.mp hv
    simpa [sub_eq_zero] using this
  have hN1 : Nat.card N = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
    · have ha := hall a.1 a.2
      have hb := hall b.1 b.2
      ext v
      rw [ha v, hb v]
  rcases hN with hN | hN <;> omega

end Main

end S143V

end CFSG.Quasithin
