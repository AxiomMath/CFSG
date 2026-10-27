module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEightRankB
public import CFSG.Quasithin.EmptyFaithful.S143VNo
public import CFSG.Quasithin.EmptyFaithful.S143WFin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN28P

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section Lift

variable (h : Hyp1281Two G T M L) (D : HatModel T M)

include h in
theorem ker_rhoH_isPGroup (hker : Hyp1281Two.centralizerHat T M ≤ T) :
    IsPGroup 2 ↥(S143V.rhoH h D).ker := by
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  intro x
  obtain ⟨k, hk⟩ := hT2 ⟨(x : ↥(mcOf T)), hker ((S143V.mem_ker_rhoH h D x).mp x.2)⟩
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun y : ↥T => (y : G)) hk))⟩

variable (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {a : G} (haV : a ∈ VZ T M)
  (haZ : a ∉ quasithinOmegaOneCenter T)

include h hU haV haZ in
theorem fix_of_overgroup
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (hker : Hyp1281Two.centralizerHat T M ≤ T)
    {A : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hAΓ : A ≤ D.img (mcOf T)) (hTA : D.img T ≤ A)
    (hidx : (D.img T).relIndex A = 3 ∨ (D.img T).relIndex A = 5) :
    ∀ α ∈ A, α (D.π a) = D.π a := by
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hker' : (S143V.rhoH h D).ker ≤ T.subgroupOf (mcOf T) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hker ((S143V.mem_ker_rhoH h D x).mp hx))
  have hmapT : (T.subgroupOf (mcOf T)).map (S143V.rhoH h D) = D.img T := S143V.map_rhoH h D hTH
  set K0 : Subgroup ↥(mcOf T) := Subgroup.comap (S143V.rhoH h D) A with hK0
  set K : Subgroup G := K0.map (mcOf T).subtype with hK
  have hrel0 : (T.subgroupOf (mcOf T)).relIndex K0 = (D.img T).relIndex A := by
    have hTP : Subgroup.comap (S143V.rhoH h D) (D.img T) = T.subgroupOf (mcOf T) := by
      rw [← hmapT, Subgroup.comap_map_eq, sup_eq_left.mpr hker']
    rw [← hTP, hK0, Subgroup.relIndex_comap, Subgroup.map_comap_eq, S143V.range_rhoH h D,
      inf_eq_right.mpr hAΓ]
  have hrelK : T.relIndex K = (D.img T).relIndex A := by
    have h1 := Subgroup.relIndex_map_map_of_injective (T.subgroupOf (mcOf T)) K0
      (mcOf T).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTH] at h1
    rw [h1]
    exact hrel0
  have hTK : T ≤ K := by
    intro t ht
    refine ⟨⟨t, hTH ht⟩, ?_, rfl⟩
    have hxN : t ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 (hTH ht)
    have : S143V.rhoH h D ⟨t, hTH ht⟩ ∈ D.img T := by
      rw [S143V.rhoH_apply h D _ hxN]
      exact HatModel.rho_mem_img ht hxN
    exact hTA this
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
  have hKM : K ≤ M := h35 K hinH (by rw [hrelK]; exact hidx)
  intro α hα
  obtain ⟨x, hxK0, hxn⟩ := S143V.exists_mem_comap_of_mem (S143V.rhoH h D)
    (S143V.range_rhoH h D ▸ hAΓ hα) hα
  have hxM : (x : G) ∈ M := hKM ⟨x, hxK0, rfl⟩
  rw [← hxn]
  exact S143V.rhoH_fix_of_mem_M h hU D haV haZ hxM


include h hU haV haZ in
theorem false_of_elem_three_two
    (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
    (hker : Hyp1281Two.centralizerHat T M ≤ T)
    {E : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hEΓ : E ≤ D.img (mcOf T)) (hE9 : Nat.card E = 9)
    (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hEfix : ∀ e ∈ E, e (D.π a) = D.π a) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := S143V.rhoH h D with hρ
  have hker2 : IsPGroup 2 ↥ρ.ker := ker_rhoH_isPGroup h D hker
  set K0 : Subgroup ↥(mcOf T) := Subgroup.comap ρ E with hK0
  let f : ↥K0 →* ↥E := (ρ.comp K0.subtype).codRestrict E (fun x => x.2)
  have hf_apply : ∀ x : ↥K0, ((f x : ↥E) : D.V ≃ₗ[ZMod 2] D.V) = ρ (x : ↥(mcOf T)) := fun _ => rfl
  have hfsurj : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ : (e : D.V ≃ₗ[ZMod 2] D.V) ∈ ρ.range := by
      rw [S143V.range_rhoH h D]
      exact hEΓ e.2
    exact ⟨⟨x, by rw [hK0, Subgroup.mem_comap, hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥K0))
  have hP3 : IsPGroup 3 ↥(P : Subgroup ↥K0) := P.isPGroup'
  have hfinj : ∀ x ∈ (P : Subgroup ↥K0), f x = 1 → x = 1 := by
    intro x hxP hfx
    have hxker : (x : ↥(mcOf T)) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hfx
    obtain ⟨k2, hk2⟩ := hker2 ⟨_, hxker⟩
    obtain ⟨k3, hk3⟩ := hP3 ⟨x, hxP⟩
    have h2 : x ^ 2 ^ k2 = 1 := Subtype.ext (by
      simpa using congrArg (fun y : ↥ρ.ker => (y : ↥(mcOf T))) hk2)
    have h3 : x ^ 3 ^ k3 = 1 := by
      simpa using congrArg (fun y : ↥(P : Subgroup ↥K0) => (y : ↥K0)) hk3
    have hd2 : orderOf x ∣ 2 ^ k2 := orderOf_dvd_of_pow_eq_one h2
    have hd3 : orderOf x ∣ 3 ^ k3 := orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime (2 ^ k2) (3 ^ k3) :=
      Nat.Coprime.pow _ _ (by norm_num)
    have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd3
    exact orderOf_eq_one_iff.mp this
  have hPcard : Nat.card (P : Subgroup ↥K0) = 9 := by
    let fP : ↥(P : Subgroup ↥K0) →* ↥E := f.comp (P : Subgroup ↥K0).subtype
    have hfPinj : Function.Injective fP := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hfinj (x : ↥K0) x.2 hx)
    have hle : Nat.card (P : Subgroup ↥K0) ≤ Nat.card E := Nat.card_le_card_of_injective fP hfPinj
    have hQ : Nat.card (P.mapSurjective hfsurj : Subgroup ↥E) =
        3 ^ (Nat.card E).factorization 3 := Sylow.card_eq_multiplicity _
    have h93 : (Nat.card E).factorization 3 = 2 := by
      rw [hE9, Nat.factorization_def _ Nat.prime_three]
      decide +kernel
    rw [Sylow.coe_mapSurjective, h93] at hQ
    have hge : Nat.card ((P : Subgroup ↥K0).map f) ≤ Nat.card (P : Subgroup ↥K0) :=
      Nat.card_le_card_of_surjective (f.subgroupMap (P : Subgroup ↥K0))
        (f.subgroupMap_surjective (P : Subgroup ↥K0))
    omega
  set S₁ : Subgroup ↥(mcOf T) := (P : Subgroup ↥K0).map K0.subtype with hS₁
  set S : Subgroup G := S₁.map (mcOf T).subtype with hS
  have hScard : Nat.card S = 3 ^ 2 := by
    rw [hS, Subgroup.card_map_of_injective (mcOf T).subtype_injective, hS₁,
      Subgroup.card_map_of_injective K0.subtype_injective, hPcard]
    norm_num
  have hSmem : ∀ s ∈ S, ∃ p ∈ (P : Subgroup ↥K0), s = (((p : ↥K0) : ↥(mcOf T)) : G) := by
    rintro _ ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hfE : ∀ p : ↥K0, ((f p : ↥E) : D.V ≃ₗ[ZMod 2] D.V) = ρ (p : ↥(mcOf T)) := fun _ => rfl
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    obtain ⟨p, hp, rfl⟩ := hSmem s hs
    obtain ⟨q, hq, rfl⟩ := hSmem t ht
    have h1 : f p * f q = f q * f p :=
      Subtype.ext (hEc _ (f p).2 _ (f q).2)
    have h2 : f (p * q * (q * p)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      exact mul_inv_cancel _
    have h3 := hfinj _ ((P : Subgroup ↥K0).mul_mem ((P : Subgroup ↥K0).mul_mem hp hq)
      ((P : Subgroup ↥K0).inv_mem ((P : Subgroup ↥K0).mul_mem hq hp))) h2
    have h4 : p * q = q * p := mul_inv_eq_one.mp h3
    show (((p : ↥K0) : ↥(mcOf T)) : G) * (((q : ↥K0) : ↥(mcOf T)) : G) =
      (((q : ↥K0) : ↥(mcOf T)) : G) * (((p : ↥K0) : ↥(mcOf T)) : G)
    have := congrArg (fun z : ↥K0 => ((z : ↥(mcOf T)) : G)) h4
    simpa using this
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := hSmem s hs
    have h1 : f (p ^ 3) = 1 := by
      rw [map_pow]
      apply Subtype.ext
      simpa using hE3 _ (f p).2
    have h2 := hfinj _ ((P : Subgroup ↥K0).pow_mem hp 3) h1
    have := congrArg (fun z : ↥K0 => ((z : ↥(mcOf T)) : G)) h2
    simpa using this
  have h13 := h.pRank_centralizerMod_le_one
  refine absurd h13 (not_le.mpr (lt_of_lt_of_le (by norm_num : 1 < 2)
    (le_pRank (by norm_num) ?_ ⟨⟨⟨fun a b => Subtype.ext (hScomm a a.2 b b.2)⟩⟩, hS3⟩ hScard)))
  intro s hs
  obtain ⟨p, hp, rfl⟩ := hSmem s hs
  have hsH : (((p : ↥K0) : ↥(mcOf T)) : G) ∈ mcOf T := ((p : ↥K0) : ↥(mcOf T)).2
  have hsN : (((p : ↥K0) : ↥(mcOf T)) : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    h.g1_le_normalizer_uOfL22 hsH
  refine ⟨hsH, Subgroup.centralizer_le_normalizer _ hsH, fun u hu => ?_⟩
  set s : G := (((p : ↥K0) : ↥(mcOf T)) : G) with hs_def
  have huU : u ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hu
  have hρs : ρ ((p : ↥K0) : ↥(mcOf T)) ∈ E := p.2
  have hrho : D.rho ⟨s, hsN⟩ = ρ ((p : ↥K0) : ↥(mcOf T)) := rfl
  have hu' : s * u * s⁻¹ ∈ uOfL22 T M := HatModel.conj_mem_uOfL22 hsN huU
  have hπ : D.π (s * u * s⁻¹) = D.π u := by
    rw [← D.rho_π ⟨s, hsN⟩ huU, hrho]
    rcases (h.hat_VZ_cases hU D haV haZ).2.2 _ (D.π_mem_hat hu huU) with h0 | h0
    · rw [h0, map_zero]
    · rw [h0]
      exact hEfix _ hρs
  have hz : (s * u * s⁻¹)⁻¹ * u ∈ centerOf (uOfL22 T M) :=
    (D.π_eq_iff _ hu' _ huU).mp hπ
  have hzV : (s * u * s⁻¹)⁻¹ * u ∈ quasithinOmegaOneCenter T := hZU ▸ hz
  have hcomm : u * ((s * u * s⁻¹)⁻¹ * u) = ((s * u * s⁻¹)⁻¹ * u) * u :=
    Subgroup.mem_centralizer_iff.mp hz.2 u huU
  have e : s * u * s⁻¹ * u⁻¹ = ((s * u * s⁻¹)⁻¹ * u)⁻¹ := by
    set w : G := s * u * s⁻¹ with hw
    have h1 : u * w⁻¹ = w⁻¹ * u := mul_right_cancel (b := u) (by simpa [mul_assoc] using hcomm)
    have h2 : w * u = u * w := by
      calc w * u = w * (u * w⁻¹) * w := by group
        _ = w * (w⁻¹ * u) * w := by rw [h1]
        _ = u * w := by group
    calc w * u⁻¹ = u⁻¹ * (u * w) * u⁻¹ := by group
      _ = u⁻¹ * (w * u) * u⁻¹ := by rw [h2]
      _ = (w⁻¹ * u)⁻¹ := by group
  rw [e]
  exact (quasithinOmegaOneCenter T).inv_mem hzV

end Lift

section Zu

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T (yOfL22 T M) g) (D : HatModel T M)

include h hU hg in
theorem zu_eq_v1_of_img_rconj_bot (hbot : D.img (rconj (centerOf (uOfL22 T M)) g) = ⊥) :
    centerOf (uOfL22 T M) = quasithinOmegaOneCenter T := by
  by_contra hne
  have hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M) :=
    lt_of_le_of_ne h.omegaOneCenter_le_centerOf_uOfL22 (Ne.symm hne)
  obtain ⟨y, hyX, hyH, hy1⟩ := S143W.exists_y₀ h hU hg D hlt
  apply hy1
  have hyN : y ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hyH
  have hmem : S143V.rhoH h D ⟨y, hyH⟩ ∈ D.img (rconj (centerOf (uOfL22 T M)) g) := by
    rw [S143V.rhoH_apply h D ⟨y, hyH⟩ hyN]
    exact HatModel.mem_img.mpr ⟨y, hyX, hyN, rfl⟩
  rw [hbot] at hmem
  exact hmem

end Zu
end SzN28P

end CFSG.Quasithin
