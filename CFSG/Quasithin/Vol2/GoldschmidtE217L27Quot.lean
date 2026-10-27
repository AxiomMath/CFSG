module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Grp
public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E217L27

section Counts

theorem le_eight_of_two_pow_dvd {a : ℕ} (h : 2 ^ a ∣ 168) : 2 ^ a ≤ 8 := by
  have hle : 2 ^ a ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have ha : a < 8 := by
    by_contra hh
    push Not at hh
    have : 2 ^ 8 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hh
    omega
  have key : ∀ m : Fin 8, 2 ^ (m : ℕ) ∣ 168 → 2 ^ (m : ℕ) ≤ 8 := by decide
  exact key ⟨a, ha⟩ h

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem card_inf_le_eight (hK : Nat.card K = 168) (hT : IsPGroup 2 T) :
    Nat.card ↥(T ⊓ K) ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hT.to_inf_left : IsPGroup 2 ↥(T ⊓ K))
  have hd : Nat.card ↥(T ⊓ K) ∣ 168 := hK ▸ Subgroup.card_dvd_of_le inf_le_right
  rw [hn] at hd ⊢
  exact le_eight_of_two_pow_dvd hd

theorem autCard_eq_card (hX : E2P.ASHyp K T M) : E2.autCard T K = Nat.card T := by
  have := hX.normal
  unfold E2.autCard
  rw [Subgroup.normalizer_eq_top, hX.cent]
  simp [Subgroup.relIndex_bot_left]

theorem index_eq_two (hX : E2P.ASHyp K T M) (hK : Nat.card K = 168)
    (hA : Nat.card (MulAut ↥K) = 336) (haut : 8 < E2.autCard T K) : K.index = 2 := by
  have := hX.normal
  have hfin : Finite (MulAut ↥K) := Nat.finite_of_card_ne_zero (by omega)
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg Subtype.val (DFunLike.congr_fun hg ⟨k, hk⟩)
      simp only [MulAut.conjNormal_apply] at this
      have h1 : g * k * g⁻¹ = k := this
      calc k * g = (g * k * g⁻¹) * g := by rw [h1]
        _ = g * k := by group
    rw [hX.cent, Subgroup.mem_bot] at hgc
    exact hgc
  have hX336 : Nat.card X ≤ 336 := hA ▸ Nat.card_le_card_of_injective _ hinj
  have h1 : Nat.card K * K.index = Nat.card X := Subgroup.card_mul_index K
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hK] at h1
  have hle : K.index ≤ 2 := by omega
  rcases (by omega : K.index = 1 ∨ K.index = 2) with h | h
  · exfalso
    have htop : K = ⊤ := Subgroup.index_eq_one.1 h
    have hTK : T ⊓ K = T := inf_eq_left.2 (htop ▸ le_top)
    have := card_inf_le_eight hK hX.minPar.isSylow.2.1
    rw [hTK, ← autCard_eq_card hX] at this
    omega
  · exact h

theorem card_inf_eq_eight (hX : E2P.ASHyp K T M) (hK : Nat.card K = 168) (hidx : K.index = 2)
    (haut : 8 < E2.autCard T K) : Nat.card ↥(T ⊓ K) = 8 := by
  have := hX.normal
  have hTN : T ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have h1 : K.relIndex (T ⊔ K) = K.relIndex T := B6.relIndex_sup_eq_of_le_normalizer hTN
  have hsup : T ⊔ K = ⊤ := by rw [sup_comm]; exact hX.sup
  rw [hsup, Subgroup.relIndex_top_right, hidx] at h1
  have h2 : K.relIndex T * Nat.card ↥(K ⊓ T) = Nat.card T := Subgroup.relIndex_mul_card K T
  rw [← h1, inf_comm] at h2
  rw [autCard_eq_card hX] at haut
  have hle := card_inf_le_eight hK hX.minPar.isSylow.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hX.minPar.isSylow.2.1.to_inf_left : IsPGroup 2 ↥(T ⊓ K))
  rw [hn] at hle h2 ⊢
  have hn4 : n < 4 := by
    by_contra hh
    push Not at hh
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hh
    omega
  interval_cases n <;> omega

end Counts

section Maximal

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem eq_of_inf_eq (hX : E2P.ASHyp K T M) (hL : L27c ↥K) (hD : Nat.card ↥(T ⊓ K) = 8)
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X)) : M = T := by
  have hKn := hX.normal
  have hTM : T ≤ M := hX.minPar.le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 ↥(T ⊓ K) := hX.minPar.isSylow.2.1.to_inf_left
  have hDnt : Nontrivial ↥(T ⊓ K) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hD]; norm_num)
  have hcn : Nontrivial ↥(Subgroup.center ↥(T ⊓ K)) := hD2.center_nontrivial
  have hcp : IsPGroup 2 ↥(Subgroup.center ↥(T ⊓ K)) := hD2.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := (hcp.nontrivial_iff_card).1 hcn
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(T ⊓ K)) := by
    rw [hn]
    exact dvd_pow_self 2 hn0.ne'
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(T ⊓ K))) 2 hdvd
  set z₀ : X := (((g : ↥(T ⊓ K)) : ↥(T ⊓ K)) : X) with hz₀def
  have hz₀2 : z₀ * z₀ = 1 := by
    have h2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have := congrArg (fun y : ↥(Subgroup.center ↥(T ⊓ K)) => ((y : ↥(T ⊓ K)) : X)) h2
    simpa [pow_two, hz₀def] using this
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    have : g = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hg
    omega
  have hz₀D : z₀ ∈ T ⊓ K := (g : ↥(T ⊓ K)).2
  have hz₀K : z₀ ∈ K := hz₀D.2
  have hz₀c : ∀ d ∈ T ⊓ K, d * z₀ = z₀ * d := by
    intro d hd
    have := Subgroup.mem_center_iff.1 g.2 ⟨d, hd⟩
    exact congrArg Subtype.val this
  have c8 : Nat.card ↥(Subgroup.centralizer ({(⟨z₀, hz₀K⟩ : ↥K)} : Set ↥K)) = 8 :=
    hL.l27.cent2 _ (Subtype.ext hz₀2) (fun h => hz₀1 (congrArg Subtype.val h))
  have hz₀Z : z₀ ∈ E2P.zOf (T ⊓ K) :=
    ⟨hz₀D, Subgroup.mem_centralizer_iff.2 fun d hd => hz₀c d hd⟩
  have hsub : (M ⊓ K).subgroupOf K ≤ Subgroup.centralizer ({(⟨z₀, hz₀K⟩ : ↥K)} : Set ↥K) := by
    intro m hm
    have hmM : (m : X) ∈ M ⊓ K := Subgroup.mem_subgroupOf.1 hm
    rw [hMK] at hmM
    have := Subgroup.mem_centralizer_iff.1 hmM.2 z₀ hz₀Z
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext this.symm
  have hle8 : Nat.card ↥(M ⊓ K) ≤ 8 := by
    have h1 := Subgroup.card_le_of_le hsub
    rw [c8] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ K ≤ K)).toEquiv] at h1
  have hDle : T ⊓ K ≤ M ⊓ K := le_inf (inf_le_left.trans hTM) inf_le_right
  have hDeq : T ⊓ K = M ⊓ K := Subgroup.eq_of_le_of_card_ge hDle (by rw [hD]; exact hle8)
  refine le_antisymm (fun m hm => ?_) hTM
  have hmtop : m ∈ T ⊔ K := by
    rw [sup_comm, hX.sup]
    exact Subgroup.mem_top m
  have hm' : m ∈ ((T ⊔ K : Subgroup X) : Set X) := hmtop
  rw [Subgroup.mul_normal T K] at hm'
  obtain ⟨t, ht, k, hk, rfl⟩ := hm'
  have hkM : k ∈ M := by
    have := M.mul_mem (M.inv_mem (hTM ht)) hm
    simpa using this
  have hkD : k ∈ T ⊓ K := hDeq ▸ ⟨hkM, hk⟩
  exact T.mul_mem ht hkD.1

omit [Finite X] in
theorem mem_of_oddOracle (hS : Setting X K) (hOdd : OddOracle K) (hD : Nat.card ↥(T ⊓ K) = 8)
    {v : X} (hv2 : v * v = 1) (hvT : ∀ t ∈ T, t * v = v * t) : v ∈ K := by
  by_contra hvK
  obtain ⟨N, hN1, hNodd, -, hNnorm⟩ := hOdd v hvK hv2
  refine false_of_order_eight hS.l27 hN1 hNodd (D := (T ⊓ K).subgroupOf K) ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv, hD]
  · intro d hd
    have hdT : (d : X) ∈ T ⊓ K := Subgroup.mem_subgroupOf.1 hd
    exact hNnorm d (hvT d hdT.1).symm

theorem centralizer_eq_of_eq (hX : E2P.ASHyp K T M) (hMT : M = T) {v : X} (hv1 : v ≠ 1)
    (hvT : ∀ t ∈ T, t * v = v * t) : Subgroup.centralizer ({v} : Set X) = T := by
  have hu : maxOver (⊤ : Subgroup X) T = {M} := hX.minPar.uniqueMax
  have hmem : M ∈ maxOver (⊤ : Subgroup X) T := by
    rw [hu]
    exact Set.mem_singleton M
  have hmax := hmem.1
  have hTC : T ≤ Subgroup.centralizer ({v} : Set X) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (hvT t ht)
  refine le_antisymm ?_ hTC
  by_contra hnle
  have hlt : M < Subgroup.centralizer ({v} : Set X) := by
    rw [hMT]
    exact lt_of_le_of_ne hTC (fun h => hnle (h ▸ le_rfl))
  have htop := hmax.2 _ hlt le_top
  have hvc : v ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k _
    have : k ∈ Subgroup.centralizer ({v} : Set X) := htop ▸ Subgroup.mem_top k
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  rw [hX.cent, Subgroup.mem_bot] at hvc
  exact hv1 hvc

end Maximal

end E217L27

end CFSG.Quasithin
