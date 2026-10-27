module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79SZ
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79D6
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Quo

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

noncomputable def Dsub : Subgroup H := J6.D6.map S.ι

theorem ι_dp : S.ι J6.d' = b₁ * b₂⁻¹ := by
  unfold J6.d'
  rw [map_mul, map_inv, S.ι_c₁, S.ι_c₂]

theorem ι_dd : S.ι J6.d = b₁ * b₂ := S.ι_d

theorem mem_Dsub_iff {x : H} : x ∈ S.Dsub ↔ ∃ ρ ∈ J6.D6fin, x = S.ι ρ := by
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, hρ, rfl⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, hρ, rfl⟩

theorem Dsub_le_J : S.Dsub ≤ J := by
  rintro _ ⟨ρ, -, rfl⟩
  exact S.ι_mem ρ

theorem Dsub_comm_beta {x : H} (hx : x ∈ S.Dsub) : x * (b₁ * b₂) = (b₁ * b₂) * x := by
  obtain ⟨ρ, hρ, rfl⟩ := S.mem_Dsub_iff.mp hx
  rw [← S.ι_dd, ← map_mul, ← map_mul, J6.D6fin_comm_d ρ hρ]

theorem c_mem_Dsub : b₁ * b₂⁻¹ ∈ S.Dsub := by
  rw [← S.ι_dp]
  exact ⟨J6.d', J6.d'_mem_D6, rfl⟩

theorem tau_mem_Dsub : S.ι J6.sg3 ∈ S.Dsub := ⟨J6.sg3, J6.sg3_mem_D6, rfl⟩

theorem Dsub_iso : Nonempty (↥S.Dsub ≃* Perm (Fin 3)) := by
  obtain ⟨e⟩ := J6.D6_iso
  exact ⟨(Subgroup.equivMapOfInjective J6.D6 S.ι S.ι_injective).symm.trans e⟩

theorem cen_J_decomp {j : H} (hj : j ∈ J) (hc : j * (b₁ * b₂) = (b₁ * b₂) * j) :
    ∃ x ∈ S.Dsub, ∃ z ∈ Subgroup.zpowers (b₁ * b₂), j = x * z := by
  obtain ⟨σ, rfl⟩ := S.exists_ι hj
  have hσ : σ * J6.d = J6.d * σ := by
    apply S.ι_injective
    rw [map_mul, map_mul, S.ι_dd]
    exact hc
  obtain ⟨ρ, hρ, k, rfl⟩ := J6.cen_d σ hσ
  refine ⟨S.ι ρ, ⟨ρ, hρ, rfl⟩, (b₁ * b₂) ^ k.val, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _, ?_⟩
  rw [map_mul, map_pow, S.ι_dd]

theorem beta_mem_J : b₁ * b₂ ∈ J := J.mul_mem S.hyp.b₁_mem S.hyp.b₂_mem

theorem Z_le_J : Subgroup.zpowers (b₁ * b₂) ≤ J := Subgroup.zpowers_le.mpr S.beta_mem_J

theorem beta_pow_three : (b₁ * b₂) ^ 3 = 1 := by
  have h : J6.d ^ 3 = 1 := J6.d_pow_three
  rw [← S.ι_dd, ← map_pow, h, map_one]

theorem beta_orderOf : orderOf (b₁ * b₂) = 3 := orderOf_eq_prime S.beta_pow_three S.d_ne_one

theorem card_Z : Nat.card (Subgroup.zpowers (b₁ * b₂)) = 3 := by
  rw [Nat.card_zpowers, S.beta_orderOf]

theorem beta_comm_b : (b₁ * b₂) * b = b * (b₁ * b₂) :=
  Subgroup.mem_centralizer_singleton_iff.mp (S.hyp.J_le_cen_b S.beta_mem_J)

theorem beta_comm_t : (b₁ * b₂) * t = t * (b₁ * b₂) := S.J_comm_t S.beta_mem_J

theorem Dsub_inf_Z : S.Dsub ⊓ Subgroup.zpowers (b₁ * b₂) = ⊥ := by
  have hβ : b₁ * b₂ ∉ S.Dsub := by
    intro hmem
    obtain ⟨ρ, hρ, hρe⟩ := S.mem_Dsub_iff.mp hmem
    have hρd : ρ = J6.d := S.ι_injective (hρe.symm.trans S.ι_dd.symm)
    exact J6.d_not_mem_D6fin (hρd ▸ hρ)
  have hcard : Nat.card (Subgroup.zpowers (b₁ * b₂)) = 3 := S.card_Z
  have hdvd : Nat.card ↥(S.Dsub ⊓ Subgroup.zpowers (b₁ * b₂)) ∣ 3 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : S.Dsub ⊓ Subgroup.zpowers (b₁ * b₂) ≤ Subgroup.zpowers (b₁ * b₂))
    rwa [hcard] at this
  apply Subgroup.eq_bot_of_card_eq
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact h1
  · exfalso
    have heq : S.Dsub ⊓ Subgroup.zpowers (b₁ * b₂) = Subgroup.zpowers (b₁ * b₂) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcard])
    apply hβ
    have : b₁ * b₂ ∈ S.Dsub ⊓ Subgroup.zpowers (b₁ * b₂) := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    exact this.1

theorem c_ne_one : b₁ * b₂⁻¹ ≠ 1 := by
  rw [← S.ι_dp]
  intro h1
  exact J6.d'_ne_one (S.ι_injective (h1.trans (map_one S.ι).symm))

theorem c_pow_three : (b₁ * b₂⁻¹) ^ 3 = 1 := by
  rw [← S.ι_dp, ← map_pow, J6.d'_pow_three, map_one]

theorem c_not_mem_Z : b₁ * b₂⁻¹ ∉ Subgroup.zpowers (b₁ * b₂) := by
  intro hc
  have : b₁ * b₂⁻¹ ∈ S.Dsub ⊓ Subgroup.zpowers (b₁ * b₂) := ⟨S.c_mem_Dsub, hc⟩
  rw [S.Dsub_inf_Z, Subgroup.mem_bot] at this
  exact S.c_ne_one this

theorem b₁_eq_cβ : b₁ = (b₁ * b₂⁻¹) * (b₁ * b₂⁻¹) * ((b₁ * b₂) * (b₁ * b₂)) := by
  have := congrArg S.ι J6.c₁_eq
  rw [S.ι_c₁, map_mul, map_mul, map_mul, S.ι_dp, S.ι_dd] at this
  exact this

theorem b₂_eq_cβ : b₂ = (b₁ * b₂⁻¹)⁻¹ * (b₁ * b₂⁻¹)⁻¹ * ((b₁ * b₂) * (b₁ * b₂)) := by
  have := congrArg S.ι J6.c₂_eq
  rw [S.ι_c₂, map_mul, map_mul, map_mul, map_inv, S.ι_dp, S.ι_dd] at this
  exact this

theorem zpowers_c_sup_Z : Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂) =
    Subgroup.closure ({b₁, b₂} : Set H) := by
  have e₁ := S.b₁_eq_cβ
  have e₂ := S.b₂_eq_cβ
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mul_mem _ S.b₁_mem_B₁ (Subgroup.inv_mem _ S.b₂_mem_B₁)
    · rw [Subgroup.zpowers_le]
      exact S.d_mem_B₁
  · rw [Subgroup.closure_le]
    intro x hx
    have hc : b₁ * b₂⁻¹ ∈ Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hβ : b₁ * b₂ ∈ Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rcases hx with hx | hx
    · have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hc) (Subgroup.mul_mem _ hβ hβ)
      rw [← e₁] at key
      rw [hx]
      exact key
    · have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc)
        (Subgroup.inv_mem _ hc)) (Subgroup.mul_mem _ hβ hβ)
      rw [← e₂] at key
      rw [hx]
      exact key

theorem isPGroup_E :
    IsPGroup 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂) : Subgroup H) := by
  have hb3 : b ^ 3 = 1 := by
    rw [← S.hyp.ord_b]
    exact pow_orderOf_eq_one b
  refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_three hb3)
    (isPGroup_zpowers_of_pow_three S.beta_pow_three) ?_
  rw [Subgroup.zpowers_le]
  exact mem_Nor_zpowers_of_comm S.beta_comm_b

theorem Nor_E_le_Nor {g : H}
    (hg : g ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂))) :
    g ∈ Nor (Subgroup.zpowers b) := by
  have hbE : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hgb := (Subgroup.mem_normalizer_iff.mp hg b).mp hbE
  exact mem_Nor_zpowers_of_conj (S.hyp.conj_mem_zpowers_of_pgroup S.isPGroup_E hbE hgb)

theorem mem_Nor_E_of_cen {g : H} (hg : g ∈ Nor (Subgroup.zpowers b))
    (hβ : g * (b₁ * b₂) = (b₁ * b₂) * g) :
    g ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)) := by
  have h2 : g ∈ Nor (Subgroup.zpowers (b₁ * b₂)) := mem_Nor_zpowers_of_comm hβ
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hg, h2⟩

theorem weak_E {h' : H}
    (hh : ∀ k : ℤ, h' * b ^ k * h'⁻¹ ∈
      Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂))) :
    h' * b * h'⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂) := by
  have h1 : h' * b * h'⁻¹ ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)) := by
    simpa using hh 1
  have hle : Subgroup.zpowers (h' * b * h'⁻¹) ≤
      Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)) := Subgroup.zpowers_le.mpr h1
  have hS : IsPGroup 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂) ⊔
      Subgroup.zpowers (h' * b * h'⁻¹) : Subgroup H) := by
    have hb3' : (h' * b * h'⁻¹) ^ 3 = 1 := by
      have hb3 : b ^ 3 = 1 := by
        rw [← S.hyp.ord_b]
        exact pow_orderOf_eq_one b
      rw [conj_pow, hb3]
      group
    exact IsPGroup.to_sup_of_normal_left' S.isPGroup_E (isPGroup_zpowers_of_pow_three hb3') hle
  have hbS : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂) ⊔
      Subgroup.zpowers (h' * b * h'⁻¹) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have hgS : h' * b * h'⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂) ⊔
      Subgroup.zpowers (h' * b * h'⁻¹) := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have := S.hyp.conj_mem_zpowers_of_pgroup hS hbS hgS
  exact Subgroup.mem_sup_left this

omit S in
theorem conj_commute_of_commute {g j x : H} (hg : g * x = x * g) (hj : j * x = x * j) :
    (g * j * g⁻¹) * x = x * (g * j * g⁻¹) := by
  have h1 : g⁻¹ * x = x * g⁻¹ := by
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hg]
      _ = x * g⁻¹ := by group
  calc (g * j * g⁻¹) * x = g * j * (g⁻¹ * x) := by group
    _ = g * j * (x * g⁻¹) := by rw [h1]
    _ = g * (j * x) * g⁻¹ := by group
    _ = g * (x * j) * g⁻¹ := by rw [hj]
    _ = (g * x) * j * g⁻¹ := by group
    _ = (x * g) * j * g⁻¹ := by rw [hg]
    _ = x * (g * j * g⁻¹) := by group

theorem N_J_aux {g : H} (hgΓ : g ∈ Cen (b₁ * b₂))
    (hg : g ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂))) {j : H}
    (hj : j ∈ S.Dsub) :
    ∃ j' ∈ S.Dsub, ∃ z ∈ Subgroup.zpowers (b₁ * b₂), g * j * g⁻¹ = j' * z := by
  have hgb := S.Nor_E_le_Nor hg
  have hgJ : g ∈ Nor J := S.hyp.N_le_NJ hgb
  have hjJ : j ∈ J := S.Dsub_le_J hj
  have hgjJ : g * j * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hgJ j).mp hjJ
  have hβg : g * (b₁ * b₂) = (b₁ * b₂) * g := Subgroup.mem_centralizer_singleton_iff.mp hgΓ
  exact S.cen_J_decomp hgjJ (conj_commute_of_commute hβg (S.Dsub_comm_beta hj))

theorem struct_b_aux : ∃ W : Subgroup H,
    W ≤ Cen (b₁ * b₂) ⊓ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)) ∧
    Nat.Coprime 3 (Nat.card W) ∧
    (∀ g ∈ Cen (b₁ * b₂) ⊓ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)),
      ∀ w ∈ W, ∃ w' ∈ W, ∃ z ∈ Subgroup.zpowers (b₁ * b₂), g * w * g⁻¹ = w' * z) ∧
    (∀ g ∈ Cen (b₁ * b₂) ⊓ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)),
      ∃ w ∈ W, ∃ y ∈ Subgroup.closure ({b, t} : Set H), ∃ j ∈ S.Dsub,
        ∃ z ∈ Subgroup.zpowers (b₁ * b₂), g = w * y * j * z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  refine ⟨Opp 3 (Nor (Subgroup.zpowers b)), ?_, L14.Opp_coprime 3 _, ?_, ?_⟩
  · intro κ hκ
    have hκβ : κ * (b₁ * b₂) = (b₁ * b₂) * κ := h.K_comm_J hκ S.beta_mem_J
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hκβ,
      S.mem_Nor_E_of_cen (L14.Opp_le 3 _ hκ) hκβ⟩
  · intro g hg w hw
    exact ⟨g * w * g⁻¹, L14.Opp_conj_mem (S.Nor_E_le_Nor hg.2) hw, 1, Subgroup.one_mem _,
      (mul_one _).symm⟩
  · intro g hg
    have hgb := S.Nor_E_le_Nor hg.2
    obtain ⟨k, hk, y, hy, j, hj, rfl⟩ := h.nor_decomp hgb
    have hβg : (k * y * j) * (b₁ * b₂) = (b₁ * b₂) * (k * y * j) :=
      Subgroup.mem_centralizer_singleton_iff.mp hg.1
    have hjβ : j * (b₁ * b₂) = (b₁ * b₂) * j := by
      have e := h.conj_eq_of_decomp hk hy hj S.beta_mem_J
      have e2 : (k * y * j) * (b₁ * b₂) * (k * y * j)⁻¹ = b₁ * b₂ := by
        rw [hβg]
        group
      rw [e2] at e
      calc j * (b₁ * b₂) = (j * (b₁ * b₂) * j⁻¹) * j := by group
        _ = (b₁ * b₂) * j := by rw [← e]
    obtain ⟨x, hx, z, hz, hjxz⟩ := S.cen_J_decomp hj hjβ
    refine ⟨k, hk, y, hy, x, hx, z, hz, ?_⟩
    rw [hjxz]
    group

theorem no2_aux {R : Subgroup H} (hRΓ : R ≤ Cen (b₁ * b₂))
    (hZR : Subgroup.zpowers (b₁ * b₂) ≤ R)
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Subgroup.zpowers (b₁ * b₂))
    (hb : b ∈ Nor R) (hc : b₁ * b₂⁻¹ ∈ Nor R) : R ≤ Subgroup.zpowers (b₁ * b₂) := by
  classical
  have hZc : ∀ r ∈ R, ∀ z ∈ Subgroup.zpowers (b₁ * b₂), r * z = z * r := by
    intro r hr z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcm : Commute r (b₁ * b₂) := Subgroup.mem_centralizer_singleton_iff.mp (hRΓ hr)
    exact (Commute.zpow_right hcm k).eq
  have hcop : ∀ r ∈ R, ∃ m : ℕ, Nat.Coprime 3 m ∧ r ^ m ∈ Subgroup.zpowers (b₁ * b₂) := by
    intro r hr
    obtain ⟨k, hk⟩ := hR2 r hr
    exact ⟨2 ^ k, Nat.Coprime.pow_right k (by norm_num), hk⟩
  obtain ⟨O, hOR, hZO, hOdec, hOc⟩ := exists_central_complement hZR hZc S.card_Z hcop
  have hO2 : IsPGroup 2 O := by
    intro x
    obtain ⟨k, hk⟩ := hR2 x.1 (hOR x.2)
    refine ⟨k, Subtype.ext ?_⟩
    have hmem : (x : H) ^ (2 ^ k) ∈ Subgroup.zpowers (b₁ * b₂) ⊓ O := ⟨hk, O.pow_mem x.2 _⟩
    rw [hZO, Subgroup.mem_bot] at hmem
    simpa using hmem
  have hNor : Nor R ≤ Nor O := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_complement hZc S.card_Z hOR hOdec hOc hx
        ((Subgroup.mem_normalizer_iff.mp hg x).mp (hOR hx))
    · intro hx
      have hxR : x ∈ R := (Subgroup.mem_normalizer_iff.mp hg x).mpr (hOR hx)
      have h1 := conj_mem_complement hZc S.card_Z hOR hOdec hOc hx
        (show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ R by simpa [mul_assoc] using hxR)
      simpa [mul_assoc] using h1
  have hβR : b₁ * b₂ ∈ R := hZR (Subgroup.mem_zpowers _)
  have hβN : b₁ * b₂ ∈ Nor R := Subgroup.le_normalizer hβR
  have hb₁ : b₁ ∈ Nor R := by
    have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hc) (Subgroup.mul_mem _ hβN hβN)
    rw [← S.b₁_eq_cβ] at key
    exact key
  have hb₂ : b₂ ∈ Nor R := by
    have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc)
      (Subgroup.inv_mem _ hc)) (Subgroup.mul_mem _ hβN hβN)
    rw [← S.b₂_eq_cβ] at key
    exact key
  have hBO : Subgroup.closure ({b, b₁, b₂} : Set H) ≤ Nor O := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hNor hb
    · exact hNor hb₁
    · exact hNor hb₂
  have hObot : O = ⊥ := S.hyp.no_two O hO2 hBO
  intro r hr
  obtain ⟨z, hz, x, hx, rfl⟩ := hOdec r hr
  rw [hObot, Subgroup.mem_bot] at hx
  rw [hx, mul_one]
  exact hz

theorem mem_CenS_B₁_iff {u : H} :
    u ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H)) ↔ u * b₁ = b₁ * u ∧ u * b₂ = b₂ * u := by
  constructor
  · intro hu
    have h1 := Subgroup.mem_centralizer_iff.mp hu b₁ S.b₁_mem_B₁
    have h2 := Subgroup.mem_centralizer_iff.mp hu b₂ S.b₂_mem_B₁
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    have hle : Subgroup.closure ({b₁, b₂} : Set H) ≤ Cen u := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h2.symm
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem CenS_B₁_le_cen_beta {u : H} (hu : u ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H))) :
    u ∈ Cen (b₁ * b₂) := by
  have h := Subgroup.mem_centralizer_iff.mp hu (b₁ * b₂) S.d_mem_B₁
  exact Subgroup.mem_centralizer_singleton_iff.mpr h.symm

theorem conj_mem_CenS_B₁ {g u : H} (hg : g ∈ Nor (Subgroup.closure ({b₁, b₂} : Set H)))
    (hu : u ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H))) :
    g * u * g⁻¹ ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H)) := by
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H) :=
    (Subgroup.mem_normalizer_iff.mp ((Nor _).inv_mem hg) y).mp hy
  have h := Subgroup.mem_centralizer_iff.mp hu _ hy'
  calc y * (g * u * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = (g * u * g⁻¹) * y := by group

theorem tau_b₁ : S.ι J6.sg3 * b₁ * (S.ι J6.sg3)⁻¹ = b₂ := by
  have := S.ι_conj J6.sg3 J6.c₁
  rw [J6.sg3_c₁_conj, S.ι_c₂, S.ι_c₁] at this
  exact this.symm

theorem tau_b₂ : S.ι J6.sg3 * b₂ * (S.ι J6.sg3)⁻¹ = b₁ := by
  have := S.ι_conj J6.sg3 J6.c₂
  rw [J6.sg3_c₂_conj, S.ι_c₁, S.ι_c₂] at this
  exact this.symm

theorem tau_mem_Nor_B₁ : S.ι J6.sg3 ∈ Nor (Subgroup.closure ({b₁, b₂} : Set H)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  have : ((MulAut.conj (S.ι J6.sg3) : MulAut H) : H →* H) '' ({b₁, b₂} : Set H) =
      ({b₂, b₁} : Set H) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl | rfl, rfl⟩
      · left
        simpa [MulAut.conj_apply] using S.tau_b₁
      · right
        simpa [MulAut.conj_apply] using S.tau_b₂
    · rintro (rfl | rfl)
      · exact ⟨b₁, Or.inl rfl, by simpa [MulAut.conj_apply] using S.tau_b₁⟩
      · exact ⟨b₂, Or.inr rfl, by simpa [MulAut.conj_apply] using S.tau_b₂⟩
  rw [this, Set.pair_comm]

theorem b₁_pow_three : b₁ ^ 3 = 1 := by
  calc b₁ ^ 3 = (S.ι J6.c₁) ^ 3 := by rw [S.ι_c₁]
    _ = S.ι (J6.c₁ ^ 3) := (map_pow S.ι _ 3).symm
    _ = 1 := by rw [J6.c₁_pow_three, map_one]

theorem b₂_pow_three : b₂ ^ 3 = 1 := by
  calc b₂ ^ 3 = (S.ι J6.c₂) ^ 3 := by rw [S.ι_c₂]
    _ = S.ι (J6.c₂ ^ 3) := (map_pow S.ι _ 3).symm
    _ = 1 := by rw [J6.c₂_pow_three, map_one]

omit S in
theorem comm_of_conj_eq {g x : H} (h : g * x * g⁻¹ = x) : g * x = x * g := by
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h]

theorem b₂_comm_b₁ : b₂ * b₁ = b₁ * b₂ :=
  S.hyp.B_comm (FS79Hyp.B₁_le_B b b₁ b₂ S.b₂_mem_B₁) (FS79Hyp.B₁_le_B b b₁ b₂ S.b₁_mem_B₁)

theorem D0_decomp {u : H} (hu : u ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H))) :
    ∃ q ∈ Opp 3 (CenS (Subgroup.closure ({b₁, b₂} : Set H))),
      ∃ m ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H)) ⊓ Nor (Subgroup.zpowers b),
        u = q * m := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  obtain ⟨hu1, hu2⟩ := S.mem_CenS_B₁_iff.mp hu
  have hQ : Ctl b b₁ (Opp 3 (Nor (Subgroup.zpowers b₁))) :=
    Ctl.of_N_bi (h.N_bi b₁ (Set.mem_insert _ _))
  have hu_nor : u ∈ Nor (Subgroup.zpowers b₁) :=
    fs79_cen_le_nor_zpowers b₁ (Subgroup.mem_centralizer_singleton_iff.mpr hu1)
  obtain ⟨q, hq, n, hn, hun⟩ := hQ.decomp u hu_nor
  have hb₁N : b₁ ∈ Nor (Subgroup.zpowers b₁) := mem_Nor_self b₁
  have hb₂N : b₂ ∈ Nor (Subgroup.zpowers b₁) := fs79_cen_le_nor_zpowers b₁
    (Subgroup.mem_centralizer_singleton_iff.mpr S.b₂_comm_b₁)
  have hqb₁ : q * b₁ * q⁻¹ = b₁ := by
    refine conj_eq_of_coprime_normal hQ.norm hQ.cop hb₁N S.b₁_pow_three S.b₁_ne_one hq ?_
    exact (Subgroup.mem_normalizer_iff.mp (hQ.le_nor hq) b₁).mp (Subgroup.mem_zpowers b₁)
  have hqb₁c : q * b₁ = b₁ * q := comm_of_conj_eq hqb₁
  have hnb₁ : n * b₁ = b₁ * n := by
    have e1 : u * b₁ = b₁ * u := hu1
    rw [hun] at e1
    have e2 : q * (n * b₁) = q * (b₁ * n) := by
      calc q * (n * b₁) = (q * n) * b₁ := by group
        _ = b₁ * (q * n) := e1
        _ = (b₁ * q) * n := by group
        _ = (q * b₁) * n := by rw [hqb₁c]
        _ = q * (b₁ * n) := by group
    exact mul_left_cancel e2
  obtain ⟨κ, hκ, y, hy, j, hj, hnkyj⟩ := h.nor_decomp hn.1
  have hjb₁ : j * b₁ = b₁ * j := by
    have e := h.conj_eq_of_decomp hκ hy hj h.b₁_mem
    rw [← hnkyj] at e
    have e' : n * b₁ * n⁻¹ = b₁ := by
      calc n * b₁ * n⁻¹ = (n * b₁) * n⁻¹ := rfl
        _ = (b₁ * n) * n⁻¹ := by rw [hnb₁]
        _ = b₁ := by group
    rw [e'] at e
    exact comm_of_conj_eq e.symm
  obtain ⟨σ, rfl⟩ := S.exists_ι hj
  have hσ : σ * J6.c₁ = J6.c₁ * σ := by
    apply S.ι_injective
    rw [map_mul, map_mul, S.ι_c₁]
    exact hjb₁
  have hn₂ : n * b₂ * n⁻¹ = b₂ ∨ n * b₂ * n⁻¹ = b₂⁻¹ := by
    have e := h.conj_eq_of_decomp hκ hy (S.ι_mem σ) h.b₂_mem
    rw [← hnkyj] at e
    rw [e]
    have := S.ι_conj σ J6.c₂
    rw [S.ι_c₂] at this
    rcases J6.cen_c₁_acts σ hσ with h1 | h1
    · left
      rw [← this, h1, S.ι_c₂]
    · right
      rw [← this, h1, map_inv, S.ι_c₂]
  have hub₂ : u * b₂ * u⁻¹ = b₂ := by
    calc u * b₂ * u⁻¹ = (b₂ * u) * u⁻¹ := by rw [hu2]
      _ = b₂ := by group
  have hqb₂mem : q * b₂ * q⁻¹ ∈ Subgroup.zpowers b₂ := by
    have e : u * b₂ * u⁻¹ = q * (n * b₂ * n⁻¹) * q⁻¹ := by rw [hun]; group
    rcases hn₂ with h1 | h1
    · rw [h1] at e
      rw [← e, hub₂]
      exact Subgroup.mem_zpowers _
    · rw [h1] at e
      have e2 : q * b₂ * q⁻¹ = b₂⁻¹ := by
        have : (q * b₂ * q⁻¹)⁻¹ = b₂ := by
          calc (q * b₂ * q⁻¹)⁻¹ = q * b₂⁻¹ * q⁻¹ := by group
            _ = b₂ := by rw [← e, hub₂]
        calc q * b₂ * q⁻¹ = ((q * b₂ * q⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
          _ = b₂⁻¹ := by rw [this]
      rw [e2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hqb₂ : q * b₂ * q⁻¹ = b₂ :=
    conj_eq_of_coprime_normal hQ.norm hQ.cop hb₂N S.b₂_pow_three S.b₂_ne_one hq hqb₂mem
  have hqD0 : q ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H)) :=
    S.mem_CenS_B₁_iff.mpr ⟨hqb₁c, comm_of_conj_eq hqb₂⟩
  have hnD0 : n ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H)) := by
    have : n = q⁻¹ * u := by rw [hun]; group
    rw [this]
    exact (CenS _).mul_mem ((CenS _).inv_mem hqD0) hu
  refine ⟨q, ?_, n, ⟨hnD0, hn.1⟩, hun⟩
  have hle : Opp 3 (Nor (Subgroup.zpowers b₁)) ⊓ CenS (Subgroup.closure ({b₁, b₂} : Set H)) ≤
      Opp 3 (CenS (Subgroup.closure ({b₁, b₂} : Set H))) := by
    refine L14.le_Opp_of_normalized inf_le_right ?_ ?_
    · intro g hg x hx
      have hgN : g ∈ Nor (Subgroup.zpowers b₁) :=
        fs79_cen_le_nor_zpowers b₁ (Subgroup.mem_centralizer_singleton_iff.mpr
          (S.mem_CenS_B₁_iff.mp hg).1)
      exact ⟨L14.Opp_conj_mem hgN hx.1, (CenS _).mul_mem ((CenS _).mul_mem hg hx.2)
        ((CenS _).inv_mem hg)⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hQ.cop
  exact hle ⟨hq, hqD0⟩

theorem fusion_cases {g : H} (hgΓ : g ∈ Cen (b₁ * b₂))
    (hg : g ∈ Nor (Subgroup.closure ({b₁, b₂} : Set H))) :
    (g * b₁ * g⁻¹ = b₁ ∧ g * b₂ * g⁻¹ = b₂) ∨ (g * b₁ * g⁻¹ = b₂ ∧ g * b₂ * g⁻¹ = b₁) := by
  have h := S.hyp
  have hβg : g * (b₁ * b₂) = (b₁ * b₂) * g := Subgroup.mem_centralizer_singleton_iff.mp hgΓ
  have h1B : g * b₁ * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ ((Subgroup.mem_normalizer_iff.mp hg b₁).mp S.b₁_mem_B₁)
  have h2B : g * b₂ * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ ((Subgroup.mem_normalizer_iff.mp hg b₂).mp S.b₂_mem_B₁)
  have f1 := h.fusion_b₁ h1B
  have f2 := h.fusion_b₂ h2B
  have hprod : (g * b₁ * g⁻¹) * (g * b₂ * g⁻¹) = b₁ * b₂ := by
    calc (g * b₁ * g⁻¹) * (g * b₂ * g⁻¹) = g * (b₁ * b₂) * g⁻¹ := by group
      _ = b₁ * b₂ := by rw [hβg]; group
  have tr : ∀ x : H, x ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H) →
      ∃ x₀ ∈ ([J6.c₁, J6.c₁⁻¹, J6.c₂, J6.c₂⁻¹] : List J6.S6), x = S.ι x₀ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · exact ⟨J6.c₁, by simp, by rw [hx, S.ι_c₁]⟩
    · exact ⟨J6.c₁⁻¹, by simp, by rw [hx, map_inv, S.ι_c₁]⟩
    · exact ⟨J6.c₂, by simp, by rw [hx, S.ι_c₂]⟩
    · exact ⟨J6.c₂⁻¹, by simp, by rw [hx, map_inv, S.ι_c₂]⟩
  obtain ⟨x₀, hx₀, hx⟩ := tr _ f1
  obtain ⟨y₀, hy₀, hy⟩ := tr _ f2
  have hxy : x₀ * y₀ = J6.d := S.ι_injective (by rw [map_mul, ← hx, ← hy, hprod, S.ι_dd])
  rcases J6.pair_eq_d x₀ hx₀ y₀ hy₀ hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨by rw [hx, h1, S.ι_c₁], by rw [hy, h2, S.ι_c₂]⟩
  · right
    exact ⟨by rw [hx, h1, S.ι_c₂], by rw [hy, h2, S.ι_c₁]⟩

theorem tau_mul_mem_CenS {g : H} (h1 : g * b₁ * g⁻¹ = b₂) (h2 : g * b₂ * g⁻¹ = b₁) :
    S.ι J6.sg3 * g ∈ CenS (Subgroup.closure ({b₁, b₂} : Set H)) := by
  rw [S.mem_CenS_B₁_iff]
  constructor
  · refine comm_of_conj_eq ?_
    calc (S.ι J6.sg3 * g) * b₁ * (S.ι J6.sg3 * g)⁻¹
        = S.ι J6.sg3 * (g * b₁ * g⁻¹) * (S.ι J6.sg3)⁻¹ := by group
      _ = b₁ := by rw [h1, S.tau_b₂]
  · refine comm_of_conj_eq ?_
    calc (S.ι J6.sg3 * g) * b₂ * (S.ι J6.sg3 * g)⁻¹
        = S.ι J6.sg3 * (g * b₂ * g⁻¹) * (S.ι J6.sg3)⁻¹ := by group
      _ = b₂ := by rw [h2, S.tau_b₁]

theorem tau_mem_D : S.ι J6.sg3 ∈ Cen (b₁ * b₂) ⊓ Nor (Subgroup.closure ({b₁, b₂} : Set H)) :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr (S.Dsub_comm_beta S.tau_mem_Dsub),
    S.tau_mem_Nor_B₁⟩

theorem struct_c_aux : ∃ Wc : Subgroup H,
    Wc ≤ Cen (b₁ * b₂) ⊓ Nor (Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂)) ∧
    Nat.Coprime 3 (Nat.card Wc) ∧
    (∀ g ∈ Cen (b₁ * b₂) ⊓ Nor (Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂)),
      ∀ w ∈ Wc, ∃ w' ∈ Wc, ∃ z ∈ Subgroup.zpowers (b₁ * b₂), g * w * g⁻¹ = w' * z) ∧
    (∀ g ∈ Cen (b₁ * b₂) ⊓ Nor (Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂)),
      ∃ w ∈ Wc, ∃ n ∈ Cen (b₁ * b₂) ⊓
          Nor (Subgroup.zpowers (b₁ * b₂⁻¹) ⊔ Subgroup.zpowers (b₁ * b₂)) ⊓
          Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)),
        ∃ z ∈ Subgroup.zpowers (b₁ * b₂), g = w * n * z) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB₁ := S.zpowers_c_sup_Z
  set B₁ : Subgroup H := Subgroup.closure ({b₁, b₂} : Set H) with hB₁def
  rw [hB₁]
  set D : Subgroup H := Cen (b₁ * b₂) ⊓ Nor B₁ with hD
  have hD0D : CenS B₁ ≤ D := fun u hu =>
    ⟨S.CenS_B₁_le_cen_beta hu, Subgroup.centralizer_le_normalizer _ hu⟩
  have hD0n : ∀ g ∈ D, ∀ c ∈ CenS B₁, g * c * g⁻¹ ∈ CenS B₁ := fun g hg c hc =>
    S.conj_mem_CenS_B₁ hg.2 hc
  have hOpp : Opp 3 (CenS B₁) ≤ Opp 3 D := L14.Opp_le_Opp_of_normalized hD0D hD0n
  refine ⟨Opp 3 D, L14.Opp_le 3 D, L14.Opp_coprime 3 D, ?_, ?_⟩
  · intro g hg w hw
    exact ⟨g * w * g⁻¹, L14.Opp_conj_mem hg hw, 1, Subgroup.one_mem _, (mul_one _).symm⟩
  · intro g hg
    have hm_mem : ∀ m ∈ CenS B₁ ⊓ Nor (Subgroup.zpowers b),
        m ∈ D ⊓ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂)) := by
      intro m hm
      have hmβ : m * (b₁ * b₂) = (b₁ * b₂) * m := by
        have := Subgroup.mem_centralizer_singleton_iff.mp (S.CenS_B₁_le_cen_beta hm.1)
        exact this
      exact ⟨hD0D hm.1, S.mem_Nor_E_of_cen hm.2 hmβ⟩
    rcases S.fusion_cases hg.1 hg.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    ·
      have hgD0 : g ∈ CenS B₁ := S.mem_CenS_B₁_iff.mpr ⟨comm_of_conj_eq h1, comm_of_conj_eq h2⟩
      obtain ⟨q, hq, m, hm, hgqm⟩ := S.D0_decomp hgD0
      exact ⟨q, hOpp hq, m, hm_mem m hm, 1, Subgroup.one_mem _, by rw [hgqm, mul_one]⟩
    ·
      have hτD : S.ι J6.sg3 ∈ D := S.tau_mem_D
      have hu := S.tau_mul_mem_CenS h1 h2
      obtain ⟨q, hq, m, hm, hum⟩ := S.D0_decomp hu
      have hτinv : (S.ι J6.sg3)⁻¹ ∈ D := D.inv_mem hτD
      have hτJ : (S.ι J6.sg3)⁻¹ ∈ Nor (Subgroup.zpowers b) :=
        S.hyp.J_le_Nor (J.inv_mem (S.ι_mem _))
      have hτβ : (S.ι J6.sg3)⁻¹ * (b₁ * b₂) = (b₁ * b₂) * (S.ι J6.sg3)⁻¹ :=
        Subgroup.mem_centralizer_singleton_iff.mp (hτinv.1)
      have hmE := hm_mem m hm
      refine ⟨(S.ι J6.sg3)⁻¹ * q * (S.ι J6.sg3)⁻¹⁻¹, ?_, (S.ι J6.sg3)⁻¹ * m, ⟨?_, ?_⟩, 1,
        Subgroup.one_mem _, ?_⟩
      · exact L14.Opp_conj_mem hτinv (hOpp hq)
      · exact D.mul_mem hτinv hmE.1
      · exact (Nor _).mul_mem (S.mem_Nor_E_of_cen hτJ hτβ) hmE.2
      · have : g = (S.ι J6.sg3)⁻¹ * (S.ι J6.sg3 * g) := by group
        rw [this, hum]
        group

theorem qdata : QData (Cen (b₁ * b₂)) (Subgroup.zpowers (b₁ * b₂)) b t (b₁ * b₂⁻¹) S.Dsub where
  Z_le := Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  Z_norm := by
    intro g hg z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcm : Commute g (b₁ * b₂) := Subgroup.mem_centralizer_singleton_iff.mp hg
    have e : g * (b₁ * b₂) ^ k = (b₁ * b₂) ^ k * g := (Commute.zpow_right hcm k).eq
    have e2 : g * (b₁ * b₂) ^ k * g⁻¹ = (b₁ * b₂) ^ k := by
      rw [e]
      group
    rw [e2]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  b_mem := Subgroup.mem_centralizer_singleton_iff.mpr S.beta_comm_b.symm
  t_mem := Subgroup.mem_centralizer_singleton_iff.mpr S.beta_comm_t.symm
  c_mem := Subgroup.mem_centralizer_singleton_iff.mpr (S.Dsub_comm_beta S.c_mem_Dsub)
  J'_le := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (S.Dsub_comm_beta hx)
  c_mem_J := S.c_mem_Dsub
  b3 := by
    rw [← S.hyp.ord_b]
    exact pow_orderOf_eq_one b
  b_nmem := fun hb => S.hyp.b_not_mem_J (S.Z_le_J hb)
  t2 := S.hyp.t_sq
  t_nmem := fun ht => S.hyp.t_not_mem_J (S.Z_le_J ht)
  tb := S.hyp.inv_b
  c3 := S.c_pow_three
  c_nmem := S.c_not_mem_Z
  J'_iso := S.Dsub_iso
  J'_inf_Z := S.Dsub_inf_Z
  J'_comm_b := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (S.hyp.J_le_cen_b (S.Dsub_le_J hj))
  J'_comm_t := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (S.hyp.J_le_cen_t (S.Dsub_le_J hj))
  N_J := fun g hg j hj => S.N_J_aux hg.1 hg.2 hj
  struct_b := S.struct_b_aux
  struct_c := S.struct_c_aux
  no2 := fun R hRΓ hZR hR2 hb hc => S.no2_aux hRΓ hZR hR2 hb hc
  weak := fun h' _ hh => S.weak_E hh

theorem Nor_beta_normalizes_cen {g c : H} (hg : g ∈ Nor (Subgroup.zpowers (b₁ * b₂)))
    (hc : c ∈ Cen (b₁ * b₂)) : g * c * g⁻¹ ∈ Cen (b₁ * b₂) := by
  have hβ' : g⁻¹ * (b₁ * b₂) * g⁻¹⁻¹ ∈ Subgroup.zpowers (b₁ * b₂) :=
    (Subgroup.mem_normalizer_iff.mp ((Nor _).inv_mem hg) _).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hβ'
  have hcm : Commute c (b₁ * b₂) := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hck : c * (b₁ * b₂) ^ k = (b₁ * b₂) ^ k * c := (Commute.zpow_right hcm k).eq
  rw [hk] at hck
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc (g * c * g⁻¹) * (b₁ * b₂)
      = g * (c * (g⁻¹ * (b₁ * b₂) * g⁻¹⁻¹)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * (b₁ * b₂) * g⁻¹⁻¹) * c) * g⁻¹ := by rw [hck]
    _ = (b₁ * b₂) * (g * c * g⁻¹) := by group

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
