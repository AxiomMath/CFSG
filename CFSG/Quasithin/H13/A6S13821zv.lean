module

public import CFSG.Quasithin.H13.A6S1372L76N3f
public import CFSG.Quasithin.H13.A6S13821z
public import CFSG.Quasithin.H13.A6S13821zh

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6S20

theorem sq_mem_of_inverts {P : Type*} [Group P] {N : Subgroup P} {σ γ n : P}
    (hσ : σ ∈ Subgroup.normalizer (N : Set P)) (hγ : γ ∈ Subgroup.normalizer (N : Set P))
    (hn : n ∈ N) (hσγ : σ * γ * σ⁻¹ * γ ∈ N) {a : P} (ha : a = n * γ ∨ a = n * γ⁻¹)
    (hσa : σ * a * σ⁻¹ * a⁻¹ ∈ N) : γ ^ 2 ∈ N := by
  have hn' : σ * n * σ⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hσ n).mp hn
  rcases ha with rfl | rfl
  ·
    have e : σ * (n * γ) * σ⁻¹ * (n * γ)⁻¹ =
        (σ * n * σ⁻¹) * (σ * γ * σ⁻¹ * γ) * (γ ^ 2)⁻¹ * n⁻¹ := by group
    rw [e] at hσa
    have h1 := N.mul_mem (N.inv_mem (N.mul_mem hn' hσγ)) (N.mul_mem hσa hn)
    have e' : ((σ * n * σ⁻¹) * (σ * γ * σ⁻¹ * γ))⁻¹ *
        ((σ * n * σ⁻¹) * (σ * γ * σ⁻¹ * γ) * (γ ^ 2)⁻¹ * n⁻¹ * n) = (γ ^ 2)⁻¹ := by group
    rw [e'] at h1
    exact N.inv_mem_iff.mp h1
  ·
    have e : σ * (n * γ⁻¹) * σ⁻¹ * (n * γ⁻¹)⁻¹ =
        (σ * n * σ⁻¹) * (γ * (σ * γ * σ⁻¹ * γ)⁻¹ * γ⁻¹) * γ ^ 2 * n⁻¹ := by group
    rw [e] at hσa
    have hm : γ * (σ * γ * σ⁻¹ * γ)⁻¹ * γ⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hγ _).mp (N.inv_mem hσγ)
    have h1 := N.mul_mem (N.inv_mem (N.mul_mem hn' hm)) (N.mul_mem hσa hn)
    have e' : ((σ * n * σ⁻¹) * (γ * (σ * γ * σ⁻¹ * γ)⁻¹ * γ⁻¹))⁻¹ *
        ((σ * n * σ⁻¹) * (γ * (σ * γ * σ⁻¹ * γ)⁻¹ * γ⁻¹) * γ ^ 2 * n⁻¹ * n) = γ ^ 2 := by group
    rwa [e'] at h1

theorem eq_one_of_commute_of_card_four {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 4)
    {α β : MulAut W} (hα3 : α ^ 3 = 1) (hfpf : ∀ w, α w = w → w = 1) (hαβ : α * β = β * α)
    {e : ℕ} (hβ : β ^ 2 ^ e = 1) : β = 1 := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hα3' : ∀ w, α (α (α w)) = w := fun w => by
    have := congrArg (fun f : MulAut W => f w) hα3
    simpa [pow_succ, MulAut.mul_apply] using this
  obtain ⟨w, hw⟩ : ∃ w : W, w ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton W := ⟨fun a b => (h a).trans (h b).symm⟩
    have h1 := Nat.card_unique (α := W)
    omega
  have hαw : α w ≠ w := fun h => hw (hfpf w h)
  have hα2w : α (α w) ≠ w := by
    intro h
    apply hw
    apply hfpf
    have h2 := congrArg α h
    rw [hα3'] at h2
    exact h2.symm
  have hα2w' : α (α w) ≠ α w := fun h => hαw (α.injective h)
  have hαw1 : α w ≠ 1 := fun h => hw (α.injective (h.trans (map_one α).symm))
  have hα2w1 : α (α w) ≠ 1 := fun h => hαw1 (α.injective (h.trans (map_one α).symm))
  have hall : ∀ v : W, v = 1 ∨ v = w ∨ v = α w ∨ v = α (α w) := by
    by_contra h
    push Not at h
    obtain ⟨v, h1, h2, h3, h4⟩ := h
    have hcard : ({1, w, α w, α (α w), v} : Finset W).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hw.symm, hαw1.symm, hα2w1.symm, h1.symm]),
        Finset.card_insert_of_notMem (by simp [hαw.symm, hα2w.symm, h2.symm]),
        Finset.card_insert_of_notMem (by simp [hα2w'.symm, h3.symm]),
        Finset.card_insert_of_notMem (by simp [h4.symm]), Finset.card_singleton]
    have hle := Finset.card_le_univ ({1, w, α w, α (α w), v} : Finset W)
    rw [hcard, ← Nat.card_eq_fintype_card, hW] at hle
    omega
  have hβα : ∀ v, β (α v) = α (β v) := fun v => by
    have := congrArg (fun f : MulAut W => f v) hαβ
    simpa [MulAut.mul_apply] using this.symm
  have hβw : β w = w ∨ β w = α w ∨ β w = α (α w) := by
    rcases hall (β w) with h | h | h | h
    · exact absurd (β.injective (h.trans (map_one β).symm)) hw
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hext : ∀ γ : MulAut W, γ * α = α * γ → γ w = w ∨ γ w = α w ∨ γ w = α (α w) →
      γ = 1 ∨ γ = α ∨ γ = α ^ 2 := by
    intro γ hγα hγw
    have hγα' : ∀ v, γ (α v) = α (γ v) := fun v => by
      have := congrArg (fun f : MulAut W => f v) hγα
      simpa [MulAut.mul_apply] using this
    have key : ∀ δ : MulAut W, δ * α = α * δ → γ w = δ w → γ = δ := by
      intro δ hδα hγδ
      have hδα' : ∀ v, δ (α v) = α (δ v) := fun v => by
        have := congrArg (fun f : MulAut W => f v) hδα
        simpa [MulAut.mul_apply] using this
      refine MulEquiv.ext fun v => ?_
      rcases hall v with rfl | rfl | rfl | rfl
      · rw [map_one, map_one]
      · exact hγδ
      · rw [hγα', hδα', hγδ]
      · rw [hγα', hγα', hδα', hδα', hγδ]
    rcases hγw with h | h | h
    · exact Or.inl (key 1 (by simp) (by simpa using h))
    · exact Or.inr (Or.inl (key α rfl h))
    · refine Or.inr (Or.inr (key (α ^ 2) (by rw [pow_succ, pow_one, mul_assoc]) ?_))
      rw [h, pow_two, MulAut.mul_apply]
  have hβα'' : β * α = α * β := hαβ.symm
  rcases hext β hβα'' hβw with h | h | h
  · exact h
  ·
    exfalso
    rw [h] at hβ
    have h3 : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
    have h2 : orderOf α ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hβ
    have h1 : orderOf α ∣ Nat.gcd 3 (2 ^ e) := Nat.dvd_gcd h3 h2
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact hαw (by rw [h1]; rfl)
  · exfalso
    rw [h, ← pow_mul] at hβ
    have h3 : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
    have h2 : orderOf α ∣ 2 * 2 ^ e := orderOf_dvd_of_pow_eq_one hβ
    have hco : Nat.Coprime 3 (2 * 2 ^ e) := by
      rw [← pow_succ']
      exact Nat.Coprime.pow_right _ (by decide)
    have h1 : orderOf α ∣ Nat.gcd 3 (2 * 2 ^ e) := Nat.dvd_gcd h3 h2
    rw [hco, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact hαw (by rw [h1]; rfl)

end A6S20

theorem eq_c3_of_odd : ∀ σ : Perm (Fin 6), σ 4 = 4 → σ 5 = 5 → σ ^ 45 = 1 →
    σ = 1 ∨ σ = swap 0 1 * swap 1 2 ∨ σ = swap 0 2 * swap 2 1 ∨ σ = swap 0 1 * swap 1 3 ∨
    σ = swap 0 3 * swap 3 1 ∨ σ = swap 0 2 * swap 2 3 ∨ σ = swap 0 3 * swap 3 2 ∨
    σ = swap 1 2 * swap 2 3 ∨ σ = swap 1 3 * swap 3 2 := by
  decide +kernel

theorem c3_of_odd (σ : Perm (Fin 6)) (h4 : σ 4 = 4) (h5 : σ 5 = 5) (h45 : σ ^ 45 = 1) :
    σ ∈ S14.C3 := by
  rcases eq_c3_of_odd σ h4 h5 h45 with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_centralizer_of_odd_13820a (hS : S.Hyp138)
    {H K : Subgroup G} (hH : H ∈ S.Hz) {c : G} (hcX : c ∈ S.X13820)
    (hc3 : c ^ 3 = 1) (hcV : c ∉ Subgroup.centralizer (V : Set G))
    (htri : ∀ y ∈ S.X13820, y ∈ pCoreOf 2 H ∨ y * c⁻¹ ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H)
    {s : G} (hsT : s ∈ T) (hsc : s * c * s⁻¹ * c ∈ pCoreOf 2 H)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {d : G} (hdK : d ∈ K) (hdH : d ∈ H)
    (hdM : d ∈ Subgroup.normalizer (L : Set G)) (hd : Odd (orderOf d)) :
    d ∈ Subgroup.centralizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X13820
  have hF := (hS.hF H hH).toHypF91
  have hTH : T ≤ H := hF.T_le_H
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hcH : c ∈ H := hL1H (P.le_L1 hcX)
  have hQT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hF.sylow_H
  have hQV : pCoreOf 2 H ≤ Subgroup.normalizer (V : Set G) := hQT.trans S.frame.T_le
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := S.inf_M_le_NV' hH ⟨hdH, hdM⟩
  set ρ := S.frame.ρ with hρdef
  set dn : ↥(Subgroup.normalizer (V : Set G)) := ⟨d, hdV⟩ with hdn
  have hdz : d * S.z * d⁻¹ = S.z := by
    have h1 : d ∈ S.G1 := hH.2.1 hdH
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  have hfix := S.fix_e0123 dn hdz
  have hodd : Odd (orderOf (ρ dn)) := by
    have h1 : orderOf (ρ dn) ∣ orderOf dn := orderOf_map_dvd _ _
    rw [hdn, Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hd h1
  have h45 : ρ dn ^ 45 = 1 := by
    have h1 : orderOf (ρ dn) ∣ 720 := by
      have h2 := orderOf_dvd_natCard (ρ dn)
      rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h2
    have hco : Nat.Coprime (orderOf (ρ dn)) 16 :=
      Nat.Coprime.pow_right 4 (Nat.coprime_two_right.mpr hodd)
    have h2 : orderOf (ρ dn) ∣ 45 :=
      hco.dvd_of_dvd_mul_left (by simpa using h1)
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  obtain ⟨h4, h5⟩ := fix45_of_odd _ hfix h45
  obtain ⟨x, hxX, hρx⟩ := P.three (ρ dn) (c3_of_odd _ h4 h5 h45)
  set N₂ : Subgroup (Perm (Fin 6)) :=
    ((pCoreOf 2 H).subgroupOf (Subgroup.normalizer (V : Set G))).map ρ with hN₂
  have hN₂2 : IsPGroup 2 ↥N₂ := by
    refine IsPGroup.map ?_ ρ
    exact (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe hQV).symm
  have hmem : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ pCoreOf 2 H → ρ g ∈ N₂ :=
    fun g hg => ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hnorm : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ H →
      ρ g ∈ Subgroup.normalizer (N₂ : Set (Perm (Fin 6))) := by
    intro g hg
    have key : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ H →
        ∀ m ∈ N₂, ρ g * m * (ρ g)⁻¹ ∈ N₂ := by
      intro g hg m hm
      obtain ⟨q, hq, rfl⟩ := hm
      refine ⟨g * q * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by
        rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) _).mp
        (Subgroup.mem_subgroupOf.mp hq)
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => key g hg m hm, fun hm => ?_⟩
    have h1 := key g⁻¹ (H.inv_mem hg) _ hm
    simpa [map_inv, mul_assoc] using h1
  have hcN : c ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le_L (P.le_L1 hcX))
  set cn : ↥(Subgroup.normalizer (V : Set G)) := ⟨c, hcN⟩ with hcn
  set sn : ↥(Subgroup.normalizer (V : Set G)) := ⟨s, S.frame.T_le hsT⟩ with hsn
  have hσγ : ρ sn * ρ cn * (ρ sn)⁻¹ * ρ cn ∈ N₂ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact hmem _ hsc
  have hσa : ρ sn * ρ dn * (ρ sn)⁻¹ * (ρ dn)⁻¹ ∈ N₂ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact hmem _ (hsK d hdK)
  have hσN := hnorm sn (hTH hsT)
  have hγN := hnorm cn hcH
  have hγ : ρ cn ^ 2 ∈ N₂ → False := by
    intro h
    obtain ⟨k, hk⟩ := hN₂2 ⟨_, h⟩
    have hk' : (ρ cn ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc3' : ρ cn ^ 3 = 1 := by
      rw [← map_pow]
      have : cn ^ 3 = 1 := Subtype.ext (by simpa using hc3)
      rw [this, map_one]
    have h1 : orderOf (ρ cn) ∣ 2 * 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, hk']
    have h2 : orderOf (ρ cn) ∣ Nat.gcd 3 (2 * 2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3') h1
    have hco : Nat.Coprime 3 (2 * 2 ^ k) := by
      rw [← pow_succ']
      exact Nat.Coprime.pow_right _ (by decide)
    rw [hco, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact hcV ((S.rho_eq_one_iff cn).mp h2)
  rcases htri (x : G) hxX with hxQ | hxc | hxc
  ·
    rw [← S.rho_eq_one_iff dn]
    have h1 : ρ dn ∈ N₂ := hρx ▸ hmem x hxQ
    obtain ⟨k, hk⟩ := hN₂2 ⟨_, h1⟩
    have hk' : ρ dn ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf (ρ dn) ∣ Nat.gcd 45 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h45) (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 45 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h2
    exact h2
  · exfalso
    have hxcn : ((x * cn⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 H := hxc
    refine hγ (A6S20.sq_mem_of_inverts hσN hγN (hmem _ hxcn) hσγ (a := ρ dn) (Or.inl ?_) hσa)
    rw [← hρx, ← map_mul, inv_mul_cancel_right]
  · exfalso
    have hxcn : ((x * cn : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 H := hxc
    refine hγ (A6S20.sq_mem_of_inverts hσN hγN (hmem _ hxcn) hσγ (a := ρ dn) (Or.inr ?_) hσa)
    rw [← hρx, ← map_inv, ← map_mul, mul_inv_cancel_right]

theorem comm_V3_of_two_13820a (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {c : G}
    (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1)
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V)
    {y : G} (hyLT : y ∈ S.L1 ⊔ T) (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1)
    (hyc : y * c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 H) :
    ∀ u ∈ S.V3, y * u * y⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  classical
  have hF := (hS.hF H hH).toHypF91
  have hLTH : S.L1 ⊔ T ≤ H := hF.L₁T_le_H
  have hLTV₁ : S.L1 ⊔ T ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hLTH.trans hF.H_normalizes_V₁
  have hLTV3 : S.L1 ⊔ T ≤ Subgroup.normalizer (S.V3 : Set G) := hF.L₁T_normalizes_Vp
  have hV3H : S.V3 ≤ H := (le_conjClosure S.V3 H).trans
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H))
  have hV3N : S.V3 ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hV3H.trans hF.H_normalizes_V₁
  have hcLT : c ∈ S.L1 ⊔ T := Subgroup.mem_sup_left hcL
  have hcard : Nat.card ↥(tildeOf (fsuV1 T V) S.V3) = 4 := by
    rw [← S.card_tilde_V3 hS hH]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (secImg_mono (le_conjClosure S.V3 H))).toEquiv).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(S.L1 ⊔ T) →* MulAut ↥(tildeOf (fsuV1 T V) S.V3),
      φ = actH hLTV₁ hLTV3 := ⟨_, rfl⟩
  have hφapp : ∀ (x : ↥(S.L1 ⊔ T)) (w : ↥(tildeOf (fsuV1 T V) S.V3)),
      ((φ x w : ↥(tildeOf (fsuV1 T V) S.V3)) :
        SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) =
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨x, hLTV₁ x.2⟩ *
        (w : SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) *
        (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨x, hLTV₁ x.2⟩)⁻¹ := by
    intro x w
    rw [hφ]
    exact actH_apply_coe hLTV₁ hLTV3 x w
  have hfix : ∀ (x : ↥(S.L1 ⊔ T)) (a : ↥(Subgroup.normalizer (fsuV1 T V : Set G)))
      (ha : (a : G) ∈ S.V3),
      φ x ⟨secMk _ _ a, secMk_mem_secImg ha⟩ = ⟨secMk _ _ a, secMk_mem_secImg ha⟩ →
      (x : G) * a * (x : G)⁻¹ * (a : G)⁻¹ ∈ fsuV1 T V := by
    intro x a ha h
    have h1 := congrArg (fun v : ↥(tildeOf (fsuV1 T V) S.V3) =>
      (v : SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) h
    simp only at h1
    rw [hφapp] at h1
    have h3 := congrArg (· * secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
      ⟨x, hLTV₁ x.2⟩) h1
    simp only [inv_mul_cancel_right] at h3
    exact commutator_mem_of_secMk_commute (x := ⟨(x : G), hLTV₁ x.2⟩) (y := a) h3
  have htriv : ∀ x : ↥(S.L1 ⊔ T),
      (∀ u ∈ S.V3, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ fsuV1 T V) → φ x = 1 := by
    intro x hx
    refine MulEquiv.ext fun w => ?_
    apply Subtype.ext
    rw [hφapp, MulAut.one_apply]
    obtain ⟨a, haV, haw⟩ := mem_secImg.mp w.2
    rw [← haw]
    have h1 := secMk_comm_of_commutator_mem
      (A := Subgroup.normalizer (fsuV1 T V : Set G)) (K := fsuV1 T V)
      (x := ⟨(x : G), hLTV₁ x.2⟩) (y := a) (hx _ haV)
    rw [h1, mul_inv_cancel_right]
  have hα3 : φ ⟨c, hcLT⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcLT⟩ : ↥(S.L1 ⊔ T)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hfpfα : ∀ w, φ ⟨c, hcLT⟩ w = w → w = 1 := by
    intro w hw
    obtain ⟨a, haV, haw⟩ := mem_secImg.mp w.2
    have hw' : w = ⟨secMk _ _ a, secMk_mem_secImg haV⟩ := Subtype.ext haw.symm
    rw [hw'] at hw ⊢
    have h5 := hfpf (a : G) (le_conjClosure S.V3 H haV) (hfix _ a haV hw)
    apply Subtype.ext
    exact (secMk_eq_one_iff).mpr h5
  have hαβ : φ ⟨c, hcLT⟩ * φ ⟨y, hyLT⟩ = φ ⟨y, hyLT⟩ * φ ⟨c, hcLT⟩ := by
    have h1 : φ (⟨y, hyLT⟩ * ⟨c, hcLT⟩ * (⟨y, hyLT⟩)⁻¹ * (⟨c, hcLT⟩)⁻¹) = 1 := by
      refine htriv _ fun u hu => ?_
      have hq : y * c * y⁻¹ * c⁻¹ ∈ centralizerMod (fsuV1 T V) H (conjClosure S.V3 H) := by
        rw [← hF.pCoreOf_eq_centralizerMod]
        exact hyc
      exact hq.2.2 u (le_conjClosure S.V3 H hu)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc φ ⟨c, hcLT⟩ * φ ⟨y, hyLT⟩
        = (φ ⟨y, hyLT⟩ * φ ⟨c, hcLT⟩ * (φ ⟨y, hyLT⟩)⁻¹ * (φ ⟨c, hcLT⟩)⁻¹)⁻¹ *
            (φ ⟨y, hyLT⟩ * φ ⟨c, hcLT⟩) := by group
      _ = φ ⟨y, hyLT⟩ * φ ⟨c, hcLT⟩ := by rw [h1, inv_one, one_mul]
  obtain ⟨e, he⟩ := hy2
  have hβ2 : φ ⟨y, hyLT⟩ ^ 2 ^ e = 1 := by
    rw [← map_pow]
    have : (⟨y, hyLT⟩ : ↥(S.L1 ⊔ T)) ^ 2 ^ e = 1 := Subtype.ext (by simpa using he)
    rw [this, map_one]
  have hβ1 := A6S20.eq_one_of_commute_of_card_four hcard hα3 hfpfα hαβ hβ2
  intro u hu
  refine hfix ⟨y, hyLT⟩ ⟨u, hV3N hu⟩ hu ?_
  rw [hβ1, MulAut.one_apply]

theorem borel_comm_V3_13820a (hS : S.Hyp138) {H K : Subgroup G}
    (hH : H ∈ S.Hz) (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hBM : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G))
    {c : G} (hcX : c ∈ S.X13820) (hc3 : c ^ 3 = 1) (hcV : c ∉ Subgroup.centralizer (V : Set G))
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V)
    (hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (htri : ∀ y ∈ S.X13820, y ∈ pCoreOf 2 H ∨ y * c⁻¹ ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H)
    {s : G} (hsT : s ∈ T) (hsc : s * c * s⁻¹ * c ∈ pCoreOf 2 H)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {b : G}
    (hb : b ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    ∀ u ∈ S.V3, b * u * b⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X13820
  have hF := (hS.hF H hH).toHypF91
  set B₀ := K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) with hB₀
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  set C' := centralizerMod (fsuV1 T V) ⊤ S.V3 with hC'
  have h2 : ∀ x ∈ B₀, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ C' := by
    intro x hx k hk
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
      rintro ⟨g, hg⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hP : IsPGroup 2 ↥((T ⊓ K) ⊔ Subgroup.zpowers x) :=
      IsPGroup.to_sup_of_normal_left' hsyl.2.1 hzp (by
        rw [Subgroup.zpowers_le]
        exact hx.2)
    have hle : (T ⊓ K) ⊔ Subgroup.zpowers x ≤ K :=
      sup_le inf_le_right (by rw [Subgroup.zpowers_le]; exact hx.1)
    have heq := hsyl.eq_of_le le_sup_left hle hP
    have hxTK : x ∈ T ⊓ K := by
      rw [← heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hyc : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 H := by
      have h1 := (pCoreOf 2 H).inv_mem (hcK x hxTK.2)
      have e : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ := by group
      rwa [e] at h1
    refine ⟨trivial, hF.H_normalizes_V₁ (hKH hxTK.2), ?_⟩
    exact S.comm_V3_of_two_13820a hS hH (P.le_L1 hcX) hc3 hfpf
      (Subgroup.mem_sup_right hxTK.1) ⟨k, hk⟩ hyc
  have hodd : ∀ x ∈ B₀, Odd (orderOf x) → x ∈ C' := by
    intro x hx hxo
    have hxV := S.mem_centralizer_of_odd_13820a hS hH hcX hc3 hcV htri hsT hsc hsK hx.1
      (hKH hx.1) (hBM hx) hxo
    refine ⟨trivial, hF.H_normalizes_V₁ (hKH hx.1), fun u hu => ?_⟩
    have h1 : x * u * x⁻¹ = u := by
      rw [← Subgroup.mem_centralizer_iff.mp hxV u (S.V3_le_V hu), mul_inv_cancel_right]
    rw [h1, mul_inv_cancel]
    exact (fsuV1 T V).one_mem
  obtain ⟨k, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
  have hb1 : (b ^ r) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have hb2 : Odd (orderOf (b ^ 2 ^ k)) := by
    have h1 : orderOf (b ^ 2 ^ k) ∣ r := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, ← hm, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hr h1
  have hcop : Nat.Coprime r (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hr)
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : b = (b ^ r) ^ x * (b ^ 2 ^ k) ^ y := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (r : ℤ) x,
      mul_comm ((2 ^ k : ℕ) : ℤ) y, hxy, zpow_one]
  have hbC : b ∈ C' := by
    rw [e]
    exact C'.mul_mem (C'.zpow_mem (h2 _ (B₀.pow_mem hb r) k hb1) x)
      (C'.zpow_mem (hodd _ (B₀.pow_mem hb _) hb2) y)
  exact hbC.2.2

end Setting4

end CFSG.Quasithin.H13.A6
