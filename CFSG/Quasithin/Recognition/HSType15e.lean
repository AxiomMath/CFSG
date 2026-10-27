module

public import CFSG.Quasithin.Recognition.HSType129f

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam

@[expose] def α0 : Equiv.Perm (Fin 6) := Equiv.swap 1 5 * Equiv.swap 2 4

@[expose] def j0 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

theorem σS0_ne_one : σS0 ≠ 1 := by decide

theorem σS0_inv_ne : σS0⁻¹ ≠ σS0 := by decide

theorem orderOf_σS0 : orderOf σS0 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime σS0_pow_three σS0_ne_one

theorem mem_zpowers_σS0 {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ Subgroup.zpowers σS0) :
    σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))) := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_σS0] at hσ
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hσ
  rw [Finset.mem_range] at hk
  interval_cases k <;> simp [sq]

theorem eq_zero_of_actS6_σS0 : ∀ u : SpV, actS6 σS0 u = u → u = 0 := by decide

theorem j0_conj : j0 * σS0 * j0⁻¹ = σS0 := by decide

theorem α0_conj : α0 * σS0 * α0⁻¹ = σS0 * σS0 := by decide

theorem j0_fpf : ∀ i, j0 i ≠ i := by decide

theorem j0_facts : ∀ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))),
    (σ * j0) ^ 3 = j0 ∧ (σ * j0) * σS0 * (σ * j0)⁻¹ = σS0 := by
  decide +kernel

theorem α0_facts : ∀ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))),
    σ * α0 ∈ lamS ∧ σ * α0 ∉ lam0 ∧ (σ * α0) * (σ * α0) = 1 ∧
      (σ * α0) * σS0 * (σ * α0)⁻¹ = σS0⁻¹ ∧
      ∃ ρ ∈ ({Equiv.swap 1 3 * Equiv.swap 2 5, Equiv.swap 1 2 * Equiv.swap 3 4,
          Equiv.swap 1 4 * Equiv.swap 3 5} : Finset (Equiv.Perm (Fin 6))),
        ρ ∈ lamS ∧ ρ * (σ * α0) * ρ⁻¹ ∈ kleinS ∧ ρ * (σ * α0) * ρ⁻¹ ≠ 1 ∧
          ∀ u : SpV, actS6 (ρ * (σ * α0) * ρ⁻¹) u = u →
            ∃ v : SpV, v + actS6 (ρ * (σ * α0) * ρ⁻¹) v = u := by
  decide +kernel

theorem exists_conj_three_of_card {G : Type*} [Group G] [Finite G] {W : Subgroup G} {m : ℕ}
    (hW : Nat.card W = 3 * m) (hm : ¬ 3 ∣ m) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    ∃ r ∈ W, r * a * r⁻¹ = b ∨ r * a * r⁻¹ = b⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a' : ↥W := ⟨a, ha⟩
  set b' : ↥W := ⟨b, hb⟩
  have hap : IsPGroup 3 ↥(Subgroup.zpowers a') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ha3, pow_one])
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers b') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hb3, pow_one])
  have hidx : ∀ c : ↥W, orderOf (c : G) = 3 → ¬ 3 ∣ (Subgroup.zpowers c).index := by
    intro c hc
    have h1 := (Subgroup.zpowers c).card_mul_index
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hc, hW] at h1
    have : (Subgroup.zpowers c).index = m := by omega
    rw [this]
    exact hm
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq ↥W (hap.toSylow (hidx _ ha3))
    (hbp.toSylow (hidx _ hb3))
  have hra : r * a' * r⁻¹ ∈ Subgroup.zpowers b' := by
    have h1 : r * a' * r⁻¹ ∈ (r • hap.toSylow (hidx _ ha3) : Sylow 3 ↥W) := by
      rw [HSSetting.mem_smul_sylow', show r⁻¹ * (r * a' * r⁻¹) * r = a' by group]
      exact Subgroup.mem_zpowers _
    rw [hr] at h1
    exact h1
  have hra' : (r : G) * a * (r : G)⁻¹ ∈ Subgroup.zpowers b := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hra
    have e := congrArg Subtype.val hj
    rw [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [← e]
    exact Subgroup.zpow_mem_zpowers b j
  refine ⟨r, r.2, ?_⟩
  rcases eq_of_mem_zpowers_three hb3 hra' with h1 | h1 | h1
  · exfalso
    have : a = 1 := by
      calc a = (r : G)⁻¹ * ((r : G) * a * (r : G)⁻¹) * r := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at ha3
    exact absurd ha3 (by decide)
  · exact Or.inl h1
  · exact Or.inr h1

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

theorem eq_one_of_mem_hsB_comm {x : ↥(hsNB z s)} (hπx : M.π x = σS0) {b : G}
    (hb : b ∈ hsB z s) (hbx : b * x = x * b) : b = 1 := by
  obtain ⟨u, rfl⟩ := M.surj b hb
  have h1 := M.act x u
  rw [hπx] at h1
  have h2 : (x : G) * M.Φ u * (x : G)⁻¹ = M.Φ u := by rw [← hbx, mul_inv_cancel_right]
  rw [h2] at h1
  rw [eq_zero_of_actS6_σS0 u (M.inj h1).symm, M.Φ_zero]

include M in
theorem exists_normalizing_lift [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s)
    (x : ↥(hsNB z s)) (hx3 : orderOf (x : G) = 3) (ρ : Equiv.Perm (Fin 6))
    (hρ : ρ * M.π x * ρ⁻¹ ∈ Subgroup.zpowers (M.π x)) :
    ∃ v : ↥(hsNB z s), (v : G) * x * (v : G)⁻¹ ∈ Subgroup.zpowers (x : G) ∧
      ∃ σ ∈ Subgroup.zpowers (M.π x), M.π v = σ * ρ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxxx : (x : G) ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  have hπx1 : M.π x ≠ 1 := by
    intro h1
    have hxB : (x : G) ∈ hsB z s := (M.ker x).mp h1
    have e := M.mul_self_of_mem_hsB hxB
    have : (x : G) = 1 := by
      calc (x : G) = (x : G) ^ 3 * ((x : G) * x)⁻¹ := by group
        _ = 1 := by rw [hxxx, e]; group
    rw [this, orderOf_one] at hx3
    exact absurd hx3 (by decide)
  have hπx3 : orderOf (M.π x) = 3 := by
    refine orderOf_eq_prime ?_ hπx1
    rw [← map_pow, show x ^ 3 = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact hxxx),
      map_one]
  set W := M.pre (Subgroup.zpowers (M.π x)) with hW
  have hcardW : Nat.card W = 48 := by
    rw [hW, M.card_pre h hsmemH hsnotK hss hg₀, Nat.card_zpowers, hπx3]
  have hxW : (x : G) ∈ W := M.mem_pre.mpr ⟨x.2, Subgroup.mem_zpowers _⟩
  obtain ⟨w₁, hw₁⟩ := M.π_surj ρ
  have hyπ : M.π (w₁ * x * w₁⁻¹) ∈ Subgroup.zpowers (M.π x) := by
    rw [map_mul, map_mul, map_inv, hw₁]
    exact hρ
  have hyW : ((w₁ * x * w₁⁻¹ : ↥(hsNB z s)) : G) ∈ W :=
    M.mem_pre.mpr ⟨(w₁ * x * w₁⁻¹).2, hyπ⟩
  have hoy : orderOf ((w₁ * x * w₁⁻¹ : ↥(hsNB z s)) : G) = 3 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      show (w₁ : G) * x * (w₁ : G)⁻¹ = MulAut.conj (w₁ : G) x from rfl, MulEquiv.orderOf_eq, hx3]
  obtain ⟨c, hcW, hc⟩ := exists_conj_three_of_card (m := 16) hcardW (by decide) hyW hxW hoy hx3
  obtain ⟨hcN, hcπ⟩ := M.mem_pre.mp hcW
  refine ⟨⟨c, hcN⟩ * w₁, ?_, M.π ⟨c, hcN⟩, hcπ, by rw [map_mul, hw₁]⟩
  have e : ((⟨c, hcN⟩ * w₁ : ↥(hsNB z s)) : G) * x * ((⟨c, hcN⟩ * w₁ : ↥(hsNB z s)) : G)⁻¹ =
      c * ((w₁ * x * w₁⁻¹ : ↥(hsNB z s)) : G) * c⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  rcases hc with hc | hc
  · rw [hc]
    exact Subgroup.mem_zpowers _
  · rw [hc]
    exact (Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)

theorem exists_x2 : ∃ x : ↥(hsNB z s), orderOf (x : G) = 3 ∧ M.π x = σS0 ∧ (x : G) ∈ M.RX := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := M.π_surj σS0
  obtain ⟨hx3, hπx⟩ := M.pow_four_cube n (by rw [hn]; exact σS0_pow_three)
  rw [hn] at hπx
  obtain ⟨x, hx⟩ : ∃ x : ↥(hsNB z s), x = n ^ 4 := ⟨_, rfl⟩
  rw [← hx] at hx3 hπx
  have hxlam : M.π x ∈ lam0 := by rw [hπx]; exact σS0_mem
  refine ⟨x, orderOf_eq_prime hx3 fun h1 => σS0_ne_one ?_, hπx, M.mem_pre.mpr ⟨x.2, hxlam⟩⟩
  rw [← hπx, show x = 1 from Subtype.ext h1, map_one]

include M in
theorem exists_j [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : ↥(hsNB z s)}
    (hx3 : orderOf (x : G) = 3) (hπx : M.π x = σS0) :
    ∃ j : G, j * j = 1 ∧ j * x = x * j ∧ ∃ g : G, g * z * g⁻¹ = j := by
  obtain ⟨v, hvx, σ, hσ, hπv⟩ := M.exists_normalizing_lift h hsmemH hsnotK hss hg₀ x hx3 j0
    (by rw [hπx, j0_conj]; exact Subgroup.mem_zpowers _)
  rw [hπx] at hσ
  obtain ⟨hv3, hvc⟩ := j0_facts σ (mem_zpowers_σS0 hσ)
  have hvx' : (v : G) * x * (v : G)⁻¹ = x := by
    rcases eq_of_mem_zpowers_three hx3 hvx with h1 | h1 | h1
    · exfalso
      have : (x : G) = 1 := by
        calc (x : G) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * v := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hx3
      exact absurd hx3 (by decide)
    · exact h1
    · exfalso
      have e : v * x * v⁻¹ = x⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, map_inv, hπx, hπv, hvc] at e'
      exact σS0_inv_ne e'.symm
  have hvx'' : (v : G) * x = x * v := by
    calc (v : G) * x = (v : G) * x * (v : G)⁻¹ * v := by group
      _ = x * v := by rw [hvx']
  have hπj : M.π (v ^ 3) = j0 := by rw [map_pow, hπv, hv3]
  have hjx : ((v ^ 3 : ↥(hsNB z s)) : G) * x = x * ((v ^ 3 : ↥(hsNB z s)) : G) := by
    rw [Subgroup.coe_pow]
    exact (Commute.pow_left (show Commute (v : G) x from hvx'') 3).eq
  have hj2 : ((v ^ 3 : ↥(hsNB z s)) : G) * ((v ^ 3 : ↥(hsNB z s)) : G) = 1 := by
    have hB : ((v ^ 3 * v ^ 3 : ↥(hsNB z s)) : G) ∈ hsB z s := (M.ker _).mp (by
      rw [map_mul, hπj, show j0 * j0 = 1 by decide])
    refine M.eq_one_of_mem_hsB_comm hπx hB ?_
    calc ((v ^ 3 : ↥(hsNB z s)) : G) * ((v ^ 3 : ↥(hsNB z s)) : G) * x =
        ((v ^ 3 : ↥(hsNB z s)) : G) * (((v ^ 3 : ↥(hsNB z s)) : G) * x) := by group
      _ = x * (((v ^ 3 : ↥(hsNB z s)) : G) * ((v ^ 3 : ↥(hsNB z s)) : G)) := by
        rw [hjx, ← mul_assoc, hjx, mul_assoc]
  refine ⟨_, hj2, hjx, ?_⟩
  exact M.conj_z_of_fpf h hsmemH hsnotK hss (n := v ^ 3) hj2 (by rw [hπj]; exact j0_fpf)

include M in
theorem exists_t1 [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : ↥(hsNB z s)}
    (hx3 : orderOf (x : G) = 3) (hπx : M.π x = σS0) :
    ∃ t : ↥(hsNB z s), (t : G) * t = 1 ∧ (t : G) * x * (t : G)⁻¹ = (x : G)⁻¹ ∧
      M.π t ∈ lamS ∧ M.π t ∉ lam0 ∧ ∃ ρ ∈ lamS, ρ * M.π t * ρ⁻¹ ∈ kleinS ∧
        ρ * M.π t * ρ⁻¹ ≠ 1 ∧ ∀ u : SpV, actS6 (ρ * M.π t * ρ⁻¹) u = u →
          ∃ v : SpV, v + actS6 (ρ * M.π t * ρ⁻¹) v = u := by
  obtain ⟨v, hvx, σ, hσ, hπv⟩ := M.exists_normalizing_lift h hsmemH hsnotK hss hg₀ x hx3 α0
    (by rw [hπx, α0_conj, ← sq]; exact Subgroup.npow_mem_zpowers _ 2)
  rw [hπx] at hσ
  obtain ⟨hl, hl0, hv2, hvinv, ρ, -, hρ⟩ := α0_facts σ (mem_zpowers_σS0 hσ)
  rw [← hπv] at hl hl0 hv2 hvinv hρ
  have hvx' : (v : G) * x * (v : G)⁻¹ = (x : G)⁻¹ := by
    rcases eq_of_mem_zpowers_three hx3 hvx with h1 | h1 | h1
    · exfalso
      have : (x : G) = 1 := by
        calc (x : G) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * v := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hx3
      exact absurd hx3 (by decide)
    · exfalso
      have e : v * x * v⁻¹ = x := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, hπx, hvinv] at e'
      exact σS0_inv_ne e'
    · exact h1
  have hv2' : (v : G) * v = 1 := by
    have hB : ((v * v : ↥(hsNB z s)) : G) ∈ hsB z s := (M.ker _).mp (by rw [map_mul, hv2])
    refine M.eq_one_of_mem_hsB_comm hπx hB ?_
    calc (v : G) * v * x = v * (v * x * (v : G)⁻¹) * (v : G)⁻¹ * (v * v) := by group
      _ = v * (x : G)⁻¹ * (v : G)⁻¹ * (v * v) := by rw [hvx']
      _ = ((v : G) * x * (v : G)⁻¹)⁻¹ * (v * v) := by group
      _ = x * (v * v) := by rw [hvx', inv_inv]
  exact ⟨v, hv2', hvx', hl, hl0, ρ, hρ.1, hρ.2⟩

include M in
theorem exists_hsB'_π [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) {κ : Equiv.Perm (Fin 6)}
    (hκ : κ ∈ kleinS) :
    ∃ b : ↥(hsNB z s), (b : G) ∈ (hsB z s).map (MulAut.conj g).toMonoidHom ∧ M.π b = κ := by
  set B' := (hsB z s).map (MulAut.conj g).toMonoidHom with hB'
  have hB'RX := M.hsB'_le_RX h hsmemH hsnotK hss hg₀ hg
  have hB'N : B' ≤ hsNB z s := hB'RX.trans (M.pre_le_hsNB _)
  set φ : ↥B' →* Equiv.Perm (Fin 6) := M.π.comp (Subgroup.inclusion hB'N) with hφ
  have hφ_apply : ∀ b : ↥B', φ b = M.π ⟨b, hB'N b.2⟩ := fun b => rfl
  have hb2 : ∀ b ∈ B', b * b = 1 := by
    intro b hb
    have hb0 : g⁻¹ * b * g ∈ hsB z s := mem_map_conj_iff.mp hb
    have e := M.mul_self_of_mem_hsB hb0
    calc b * b = g * (g⁻¹ * b * g * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hrange : φ.range ≤ kleinS := by
    rintro _ ⟨b, rfl⟩
    rw [hφ_apply]
    have hl0 : M.π ⟨b, hB'N b.2⟩ ∈ lam0 := M.π_mem_of_mem_pre (hB'RX b.2) (hB'N b.2)
    refine mem_kleinS_of_lam0 _ hl0 ?_
    rw [← map_mul]
    refine (M.ker _).mpr ?_
    show (b : G) * b ∈ hsB z s
    rw [hb2 b b.2]
    exact (hsB z s).one_mem
  have hker : Nat.card φ.ker ≤ 4 := by
    have hinj : Function.Injective (fun k : ↥φ.ker => (⟨((k : ↥B') : G), by
        have hk : M.π ⟨(k : ↥B'), hB'N (k : ↥B').2⟩ = 1 := k.2
        rw [← M.hsB_inf_hsB' h hsmemH hsnotK hss hg₀ hg hgNN]
        exact ⟨(M.ker _).mp hk, (k : ↥B').2⟩⟩ : ↥M.V2)) := by
      intro k k' e
      have e' := congrArg (Subtype.val : ↥M.V2 → G) e
      exact Subtype.ext (Subtype.ext e')
    have := Nat.card_le_card_of_injective _ hinj
    rwa [M.card_V2] at this
  have hcardB' : Nat.card B' = 16 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj g).injective,
      h.card_hsB hsmemH hsnotK hss]
  have hprod : Nat.card φ.range * Nat.card φ.ker = 16 := by
    rw [← hcardB', Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hge : 4 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.range * Nat.card φ.ker ≤ 3 * 4 :=
      Nat.mul_le_mul (by omega) hker
    omega
  have heq : φ.range = kleinS :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [card_kleinS]; exact hge)
  rw [← heq] at hκ
  obtain ⟨b, hb⟩ := hκ
  exact ⟨⟨b, hB'N b.2⟩, b.2, hb⟩

include M in
theorem conj_z_of_kleinS [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) {t : ↥(hsNB z s)}
    (htt : (t : G) * t = 1) (hκ : M.π t ∈ kleinS) (hκ1 : M.π t ≠ 1)
    (hfib : ∀ u : SpV, actS6 (M.π t) u = u → ∃ v : SpV, v + actS6 (M.π t) v = u) :
    ∃ g' : G, g' * z * g'⁻¹ = t := by
  obtain ⟨b, hbB', hbπ⟩ := M.exists_hsB'_π h hsmemH hsnotK hss hg₀ hg hgNN hκ
  have hker : ((t * b⁻¹ : ↥(hsNB z s)) : G) ∈ hsB z s :=
    (M.ker _).mp (by rw [map_mul, map_inv, hbπ, mul_inv_cancel])
  obtain ⟨w, hw⟩ := M.surj _ hker
  have htw : (t : G) = M.Φ w * b := by
    rw [hw, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hb0 : g⁻¹ * b * g ∈ hsB z s := mem_map_conj_iff.mp hbB'
  have hb2 : (b : G) * b = 1 := by
    have e := M.mul_self_of_mem_hsB hb0
    calc (b : G) * b = g * (g⁻¹ * b * g * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hact : ∀ u, (b : G) * M.Φ u * (b : G)⁻¹ = M.Φ (actS6 (M.π t) u) := fun u => by
    rw [M.act b u, hbπ]
  have hsum : w + actS6 (M.π t) w = 0 := by
    refine M.Φ_eq_one ?_
    rw [M.add, ← hact]
    calc M.Φ w * ((b : G) * M.Φ w * (b : G)⁻¹) =
        (M.Φ w * b) * (M.Φ w * b) * ((b : G) * b)⁻¹ := by group
      _ = 1 := by rw [← htw, htt, hb2]; group
  have hwfix : actS6 (M.π t) w = w := by
    calc actS6 (M.π t) w = (w + actS6 (M.π t) w) + w := by
          rw [add_comm w (actS6 (M.π t) w), add_assoc, spV_add_self, add_zero]
      _ = w := by rw [hsum, zero_add]
  obtain ⟨v, hv⟩ := hfib w hwfix
  have hcb : M.Φ v * b * (M.Φ v)⁻¹ = t := by
    rw [M.Φ_inv, htw, ← hv, M.add, ← hact v]
    group
  have hb1 : g⁻¹ * b * g ≠ 1 := by
    intro h1
    have hb1' : (b : G) = 1 := by
      calc (b : G) = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    apply hκ1
    rw [← hbπ, show b = 1 from Subtype.ext hb1', map_one]
  obtain ⟨n, -, hn⟩ := h.exists_normalizer_conj_hsB hsmemH hsnotK hss hg₀ hb0 hb1
  refine ⟨M.Φ v * g * n, ?_⟩
  rw [← hcb]
  calc M.Φ v * g * n * z * (M.Φ v * g * n)⁻¹ =
      M.Φ v * (g * (n * z * n⁻¹) * g⁻¹) * (M.Φ v)⁻¹ := by group
    _ = M.Φ v * b * (M.Φ v)⁻¹ := by rw [hn]; group

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
