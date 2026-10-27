module

public import CFSG.Quasithin.EmptyFaithful.S143VNo
public import CFSG.Quasithin.EmptyFaithful.S143Struct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143W

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section CP

variable (h : Hyp1281Two G T M L) {P : Subgroup G} (hPH : P ≤ mcOf T)
  (hPn : ∀ x ∈ mcOf T, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
  (hPZ : ∀ p ∈ P, ∀ z ∈ centerOf (uOfL22 T M), p * z = z * p)

include h hPH hPn hPZ in
theorem inf_centralizerHat_le_pCore :
    P ⊓ Hyp1281Two.centralizerHat T M ≤ pCoreOf 2 (mcOf T) := by
  classical
  set R := Hyp1281Two.centralizerHat T M with hR
  set Q := pCoreOf 2 (mcOf T) with hQ
  have hsq : ∀ x ∈ P ⊓ R, x ^ 2 ∈ Q := by
    rintro x ⟨hxP, hxR⟩
    rw [hQ, ← Hyp1281Two.lemma_12_8_4_four h h.isHz_centralizer]
    have hxH : x ∈ mcOf T := hPH hxP
    refine ⟨Subgroup.pow_mem _ hxH 2, ?_, fun u hu => ?_⟩
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.pow_mem _ hxH 2)
    · set c := x * u * x⁻¹ * u⁻¹ with hc
      have hcZU : c ∈ centerOf (uOfL22 T M) := hxR.2.2 u hu
      have hcU : c ∈ uOfL22 T M := hcZU.1
      have hxc : x * c = c * x := hPZ x hxP c hcZU
      have e : x ^ 2 * u * (x ^ 2)⁻¹ * u⁻¹ = c ^ 2 := by
        have h1 : x * u * x⁻¹ = c * u := by rw [hc]; group
        calc x ^ 2 * u * (x ^ 2)⁻¹ * u⁻¹ = x * (x * u * x⁻¹) * x⁻¹ * u⁻¹ := by
              simp only [pow_two]; group
          _ = x * (c * u) * x⁻¹ * u⁻¹ := by rw [h1]
          _ = (x * c * x⁻¹) * (x * u * x⁻¹) * u⁻¹ := by group
          _ = c * (c * u) * u⁻¹ := by
              have : x * c * x⁻¹ = c := by
                calc x * c * x⁻¹ = (c * x) * x⁻¹ := by rw [hxc]
                  _ = c := by group
              rw [this, h1]
          _ = c ^ 2 := by simp only [pow_two]; group
      rw [e]
      exact h.sq_mem_omegaOneCenter hcU
  have hnorm : ∀ y ∈ mcOf T, ∀ s ∈ P ⊓ R, y * s * y⁻¹ ∈ P ⊓ R := by
    intro y hy s hs
    refine ⟨hPn y hy s hs.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (h.centralizer_le_normalizer_centralizerHat hy) s).mp hs.2
  have h2 : IsPGroup 2 ↥(P ⊓ R) := by
    intro s
    have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
    have hs2 : (s : G) ^ 2 ∈ Q := hsq s s.2
    obtain ⟨k, hk⟩ := hQp ⟨(s : G) ^ 2, hs2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((s : G) ^ 2) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    show (s : G) ^ 2 ^ (k + 1) = 1
    rw [pow_succ, mul_comm, pow_mul]
    exact hk'
  have hSQ : P ⊓ R ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hPH)
      (fun y hy => (Subgroup.mem_normalizer_iff).mpr fun s =>
        ⟨fun hs => hnorm y hy s hs, fun hs => by
          have := hnorm y⁻¹ (Subgroup.inv_mem _ hy) _ hs
          simpa [mul_assoc] using this⟩) h2
  exact hSQ

include h hPH hPn hPZ in
theorem inf_centralizerHat_le_T : P ⊓ Hyp1281Two.centralizerHat T M ≤ T :=
  (inf_centralizerHat_le_pCore h hPH hPn hPZ).trans (S143.qOf_le_T_of_hyp h)

end CP

section Gen

variable {H S : Type*} [Group H] [Group S] [Finite S] (ρ : H →* S)

theorem relIndex_sup_of_ker {T₀ K' : Subgroup H}
    (hnorm : ∀ t ∈ T₀, ∀ k ∈ K', t * k * t⁻¹ ∈ K')
    (hNT : ∀ x ∈ K'.map ρ, x ∈ T₀.map ρ → x = 1)
    (hker : ∀ k ∈ K', ρ k = 1 → k ∈ T₀) :
    T₀.relIndex (K' ⊔ T₀) = Nat.card (K'.map ρ) := by
  classical
  have hprod : ∀ x ∈ K' ⊔ T₀, ∃ t ∈ T₀, ∃ k ∈ K', x = t * k := by
    let A : Subgroup H :=
      { carrier := {x | ∃ t ∈ T₀, ∃ k ∈ K', x = t * k}
        mul_mem' := by
          rintro _ _ ⟨t, ht, k, hk, rfl⟩ ⟨t', ht', k', hk', rfl⟩
          refine ⟨t * t', T₀.mul_mem ht ht', (t'⁻¹ * k * t') * k', K'.mul_mem ?_ hk', ?_⟩
          · have := hnorm t'⁻¹ (T₀.inv_mem ht') k hk
            simpa using this
          · group
        one_mem' := ⟨1, T₀.one_mem, 1, K'.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨t, ht, k, hk, rfl⟩
          refine ⟨t⁻¹, T₀.inv_mem ht, t * k⁻¹ * t⁻¹, ?_, ?_⟩
          · exact hnorm t ht k⁻¹ (K'.inv_mem hk)
          · group }
    have hle : K' ⊔ T₀ ≤ A := sup_le (fun k hk => ⟨1, T₀.one_mem, k, hk, by simp⟩)
      (fun t ht => ⟨t, ht, 1, K'.one_mem, by simp⟩)
    exact fun x hx => hle hx
  set J : Subgroup H := K' ⊔ T₀ with hJ
  have hK'J : K' ≤ J := le_sup_left
  have hT₀J : T₀ ≤ J := le_sup_right
  let ρ₁ : ↥J →* S := ρ.comp J.subtype
  let T₁ : Subgroup ↥J := T₀.subgroupOf J
  have hmapT : T₁.map ρ₁ = T₀.map ρ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hT₀J hx⟩, hx, rfl⟩
  have hker₁ : ρ₁.ker ≤ T₁ := by
    intro x hx
    have hx1 : ρ (x : H) = 1 := hx
    obtain ⟨t, ht, k, hk, hxe⟩ := hprod x x.2
    have hk1 : ρ k = 1 := by
      have h1 : ρ k ∈ K'.map ρ := ⟨k, hk, rfl⟩
      have h2 : ρ k ∈ T₀.map ρ := by
        have : ρ k = (ρ t)⁻¹ := by
          have : ρ (t * k) = 1 := by rw [← hxe]; exact hx1
          rw [map_mul] at this
          exact eq_inv_of_mul_eq_one_right this
        rw [this]
        exact (T₀.map ρ).inv_mem ⟨t, ht, rfl⟩
      exact hNT _ h1 h2
    have hkT : k ∈ T₀ := hker k hk hk1
    show (x : H) ∈ T₀
    rw [hxe]
    exact T₀.mul_mem ht hkT
  have hNr : K'.map ρ ≤ ρ₁.range := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, hK'J hk⟩, rfl⟩
  have hNn : ∀ s ∈ ρ₁.range, ∀ n ∈ K'.map ρ, s * n * s⁻¹ ∈ K'.map ρ := by
    rintro _ ⟨x, rfl⟩ _ ⟨k, hk, rfl⟩
    obtain ⟨t, ht, k₂, hk₂, hxe⟩ := hprod x x.2
    refine ⟨(x : H) * k * (x : H)⁻¹, ?_, by simp [ρ₁]⟩
    rw [hxe]
    have h1 : k₂ * k * k₂⁻¹ ∈ K' := K'.mul_mem (K'.mul_mem hk₂ hk) (K'.inv_mem hk₂)
    have h2 := hnorm t ht _ h1
    have e : t * k₂ * k * (t * k₂)⁻¹ = t * (k₂ * k * k₂⁻¹) * t⁻¹ := by group
    rw [e]
    exact h2
  have hNT₁ : ∀ x ∈ K'.map ρ, x ∈ T₁.map ρ₁ → x = 1 := by
    intro x hx hxT
    rw [hmapT] at hxT
    exact hNT x hx hxT
  have hidx := S143V.relIndex_comap_sup_map ρ₁ hker₁ hNr hNn hNT₁
  have htop : Subgroup.comap ρ₁ (K'.map ρ ⊔ T₁.map ρ₁) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht, k, hk, hxe⟩ := hprod x x.2
    have : ρ₁ x = ρ t * ρ k := by
      show ρ (x : H) = _
      rw [hxe, map_mul]
    rw [Subgroup.mem_comap, this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨⟨t, hT₀J ht⟩, ht, rfl⟩)
      (Subgroup.mem_sup_left ⟨k, hk, rfl⟩)
  rw [htop, Subgroup.relIndex_top_right] at hidx
  exact hidx

end Gen

section Main

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
  (haZ : a ∉ quasithinOmegaOneCenter T)

include h hU hg haV haZ in
theorem no_normal_three_five_of_P
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    {P : Subgroup G} (hPH : P ≤ mcOf T) (hPn : ∀ x ∈ mcOf T, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hPT : P ⊓ Hyp1281Two.centralizerHat T M ≤ T)
    {N : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hNP : N ≤ D.img P)
    (hNn : ∀ γ ∈ D.img (mcOf T), ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hN : Nat.card N = 3 ∨ Nat.card N = 5) : False := by
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hrange : (S143V.rhoH h D).range = D.img (mcOf T) := S143V.range_rhoH h D
  have hmapT : (T.subgroupOf (mcOf T)).map (S143V.rhoH h D) = D.img T := S143V.map_rhoH h D hTH
  have hP2 : IsPGroup 2 ↥(D.img T) := (S143V.isSylowTwoOf_img_T h D).2.1
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
  set ρ := S143V.rhoH h D with hρ
  set T₀ : Subgroup ↥(mcOf T) := T.subgroupOf (mcOf T) with hT₀
  set K'₀ : Subgroup ↥(mcOf T) := P.subgroupOf (mcOf T) ⊓ Subgroup.comap ρ N with hK'₀
  have hnorm : ∀ t ∈ T₀, ∀ k ∈ K'₀, t * k * t⁻¹ ∈ K'₀ := by
    intro t ht k hk
    refine ⟨?_, ?_⟩
    · exact hPn (t : G) t.2 (k : G) hk.1
    · have h1 : ρ t ∈ D.img (mcOf T) := by
        rw [← hrange]
        exact ⟨t, rfl⟩
      have h2 : ρ k ∈ N := hk.2
      have h3 := hNn _ h1 _ h2
      show ρ (t * k * t⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact h3
  have hmapK : K'₀.map ρ = N := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · intro n hn
      obtain ⟨x, hxP, hxN, hxρ⟩ := HatModel.mem_img.mp (hNP hn)
      have hxH : x ∈ mcOf T := hPH hxP
      refine ⟨⟨x, hxH⟩, ⟨hxP, ?_⟩, ?_⟩
      · show ρ ⟨x, hxH⟩ ∈ N
        rw [S143V.rhoH_apply h D _ hxN, hxρ]
        exact hn
      · rw [S143V.rhoH_apply h D _ hxN]
        exact hxρ
  have hNT' : ∀ x ∈ K'₀.map ρ, x ∈ T₀.map ρ → x = 1 := by
    intro x hx hxT
    rw [hmapK] at hx
    rw [hmapT] at hxT
    exact hNT x hx hxT
  have hker : ∀ k ∈ K'₀, ρ k = 1 → k ∈ T₀ := by
    intro k hk hk1
    have hkR : (k : G) ∈ Hyp1281Two.centralizerHat T M := (S143V.mem_ker_rhoH h D k).mp hk1
    exact hPT ⟨hk.1, hkR⟩
  have hidx : T₀.relIndex (K'₀ ⊔ T₀) = Nat.card N := by
    rw [relIndex_sup_of_ker ρ hnorm hNT' hker, hmapK]
  set K : Subgroup G := (K'₀ ⊔ T₀).map (mcOf T).subtype with hK
  have hrelK : T.relIndex K = Nat.card N := by
    have h1 := Subgroup.relIndex_map_map_of_injective T₀ (K'₀ ⊔ T₀) (mcOf T).subtype_injective
    rw [hT₀, Subgroup.map_subgroupOf_eq_of_le hTH] at h1
    rw [h1]
    exact hidx
  have hTK : T ≤ K := by
    intro t ht
    exact ⟨⟨t, hTH ht⟩, Subgroup.mem_sup_right (show (⟨t, hTH ht⟩ : ↥(mcOf T)) ∈ T₀ from ht), rfl⟩
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
    rw [← hmapK] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    have hkK : (k : G) ∈ K := ⟨k, Subgroup.mem_sup_left hk, rfl⟩
    exact S143V.rhoH_fix_of_mem_M h hU D haV haZ (hKM hkK)
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

end S143W

end CFSG.Quasithin
