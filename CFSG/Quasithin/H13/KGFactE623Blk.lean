module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender

public section

namespace CFSG.Quasithin.H13.KGE623

open CFSG.QuasithinUnique Equiv

@[expose] def fix34 : Subgroup (alternatingGroup (Fin 5)) :=
  (MulAction.stabilizer (Perm (Fin 5)) (3 : Fin 5) ⊓
    MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)).comap (alternatingGroup (Fin 5)).subtype

theorem mem_fix34 {σ : alternatingGroup (Fin 5)} :
    σ ∈ fix34 ↔ (σ : Perm (Fin 5)) 3 = 3 ∧ (σ : Perm (Fin 5)) 4 = 4 :=
  Iff.rfl

@[expose] def c3 : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def r2 : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 3 4, Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem c3_mem_fix34 : c3 ∈ fix34 :=
  mem_fix34.mpr (by decide +kernel)

theorem orderOf_c3 : orderOf c3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
  · show (swap (0 : Fin 5) 1 * swap 1 2) ^ 3 = 1
    decide +kernel
  · have h' : (swap (0 : Fin 5) 1 * swap 1 2 : Perm (Fin 5)) = 1 := congrArg Subtype.val h
    revert h'
    decide +kernel

theorem mul_r2_ne : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ 3 = 3 → σ 4 = 4 → σ ≠ 1 →
    σ * (swap 0 1 * swap 3 4) ≠ (swap 0 1 * swap 3 4) * σ := by
  decide +kernel

@[expose] def v1 : Fin 5 → ZMod 2 := ![0, 0, 0, 1, 1]

@[expose] def v2 : Fin 5 → ZMod 2 := ![1, 1, 1, 1, 0]

theorem v1_mem : v1 ∈ evenWeight 5 :=
  (A5.Delta5.mem_evenWeight_iff v1).mpr (by decide +kernel)

theorem v2_mem : v2 ∈ evenWeight 5 :=
  (A5.Delta5.mem_evenWeight_iff v2).mpr (by decide +kernel)

theorem fix_v : ∀ σ : Perm (Fin 5), σ 3 = 3 → σ 4 = 4 →
    ∀ i, v1 (σ⁻¹ i) = v1 i ∧ v2 (σ⁻¹ i) = v2 i := by
  decide +kernel

theorem v_ne : v1 ≠ 0 ∧ v2 ≠ 0 ∧ v1 + v2 ≠ 0 := by
  decide +kernel

theorem conj_eq_of_pow_three {G : Type*} [Group G] {x w z : G} (hx : x ^ 3 = 1)
    (hxw : x * w * x⁻¹ = z * w) (hzx : z * x = x * z) (hz : z ^ 2 = 1) :
    x * w * x⁻¹ = w := by
  have hxz : x * z * x⁻¹ = z := by rw [← hzx]; group
  have h1 : x * (x * w * x⁻¹) * x⁻¹ = w := by
    calc x * (x * w * x⁻¹) * x⁻¹ = x * (z * w) * x⁻¹ := by rw [hxw]
      _ = (x * z * x⁻¹) * (x * w * x⁻¹) := by group
      _ = z * (z * w) := by rw [hxz, hxw]
      _ = z ^ 2 * w := by rw [sq, mul_assoc]
      _ = w := by rw [hz, one_mul]
  have h2 : x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = w := by
    calc x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * w * (x ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = w := by rw [hx]; group
  rwa [h1] at h2

variable {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y}

omit [Finite Y] in
theorem eq_one_of_mem_centralizer (β : blockU B →* Multiplicative (evenWeight 5))
    (hβk : β.ker = (blockZ B).subgroupOf (blockU B)) (u : blockU B)
    (hu : (u : Y) ∈ Subgroup.centralizer (B : Set Y)) : β u = 1 := by
  have h : u ∈ β.ker := by
    rw [hβk, Subgroup.mem_subgroupOf]
    exact ⟨u.2, hu⟩
  exact h

theorem exists_elements (hS : IsShort2 B) (hA : IsAltType B 5) :
    ∃ x ∈ B, x ^ 3 = 1 ∧ x ∉ Subgroup.centralizer (B : Set Y) ∧
      ∃ w₁ ∈ blockU B, ∃ w₂ ∈ blockU B, x * w₁ = w₁ * x ∧ x * w₂ = w₂ * x ∧
        w₁ ∉ Subgroup.centralizer (B : Set Y) ∧ w₂ ∉ Subgroup.centralizer (B : Set Y) ∧
        w₁ * w₂ ∉ Subgroup.centralizer (B : Set Y) := by
  classical
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := hA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup B := fix34.comap α with hH
  have hHmap : H.map α = fix34 := Subgroup.map_comap_eq_self_of_surjective hα fix34
  have h3 : 3 ∣ Nat.card H := by
    have h1 : 3 ∣ Nat.card fix34 := by
      have h := orderOf_dvd_natCard (⟨c3, c3_mem_fix34⟩ : fix34)
      rwa [Subgroup.orderOf_mk, orderOf_c3] at h
    have h2 : Nat.card fix34 ∣ Nat.card H := hHmap ▸ Subgroup.card_map_dvd H α
    exact h1.trans h2
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h3
  set ℓ : B := (h : B) with hℓdef
  have hℓ3 : orderOf ℓ = 3 := by rw [hℓdef, Subgroup.orderOf_coe, hh]
  have hℓH : α ℓ ∈ fix34 := h.2
  have hαℓ : α ℓ ≠ 1 := by
    intro h1
    have hk : ℓ ∈ CFSG.pCore 2 B := by
      rw [← hαk]
      exact h1
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := B) ⟨ℓ, hk⟩
    have hn' : ℓ ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hd := orderOf_dvd_of_pow_eq_one hn'
    rw [hℓ3] at hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  set x : Y := (ℓ : Y) with hxdef
  have hxB : x ∈ B := ℓ.2
  have hx3 : x ^ 3 = 1 := by
    have h1 : ℓ ^ 3 = 1 := by rw [← hℓ3]; exact pow_orderOf_eq_one ℓ
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hxC : x ∉ Subgroup.centralizer (B : Set Y) := by
    intro hC
    obtain ⟨b, hb⟩ := hα r2
    have hcomm : ℓ * b = b * ℓ :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hC) (b : Y) b.2).symm
    have h1 := congrArg α hcomm
    rw [map_mul, map_mul, hb] at h1
    have h2 : ((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) * (swap 0 1 * swap 3 4) =
        (swap 0 1 * swap 3 4) * ((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) :=
      congrArg Subtype.val h1
    exact mul_r2_ne _ (Perm.mem_alternatingGroup.mp (α ℓ).2) (mem_fix34.mp hℓH).1
      (mem_fix34.mp hℓH).2 (fun h0 => hαℓ (Subtype.ext h0)) h2
  have key : ∀ (u : blockU B) (v : Fin 5 → ZMod 2) (hv : v ∈ evenWeight 5),
      β u = Multiplicative.ofAdd ⟨v, hv⟩ →
      (∀ i, v (((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5))⁻¹ i) = v i) →
      x * u = u * x := by
    intro u v hv hu hfix
    have hconj : x * (u : Y) * x⁻¹ ∈ blockU B :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hxB) u).mp u.2
    set u' : blockU B := ⟨x * u * x⁻¹, hconj⟩ with hu'
    have he := hβe ℓ u u' rfl
    have hβ' : β u' = β u := by
      rw [hu]
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      rw [he i, hu]
      exact hfix i
    have hk : u' * u⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβ', mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hk
    have hk' : x * (u : Y) * x⁻¹ * (u : Y)⁻¹ ∈
        blockU B ⊓ Subgroup.centralizer (B : Set Y) := hk
    obtain ⟨hzU, hzC⟩ := hk'
    have hz2 := C1.blockU_sq hS _ hzU
    have hzx : x * (u : Y) * x⁻¹ * (u : Y)⁻¹ * x = x * (x * (u : Y) * x⁻¹ * (u : Y)⁻¹) :=
      ((Subgroup.mem_centralizer_iff.mp hzC) x hxB).symm
    have h1 := conj_eq_of_pow_three (w := (u : Y)) hx3 (by group) hzx hz2
    calc x * (u : Y) = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [h1]
  have hfix := fix_v _ (mem_fix34.mp hℓH).1 (mem_fix34.mp hℓH).2
  obtain ⟨u₁, hu₁⟩ := hβ (Multiplicative.ofAdd ⟨v1, v1_mem⟩)
  obtain ⟨u₂, hu₂⟩ := hβ (Multiplicative.ofAdd ⟨v2, v2_mem⟩)
  obtain ⟨hv1, hv2, hv12⟩ := v_ne
  have hnot : ∀ u : blockU B, ∀ v : Fin 5 → ZMod 2, ∀ hv : v ∈ evenWeight 5,
      β u = Multiplicative.ofAdd ⟨v, hv⟩ → v ≠ 0 →
      (u : Y) ∉ Subgroup.centralizer (B : Set Y) := by
    intro u v hv hu hv0 hC
    have h1 := eq_one_of_mem_centralizer β hβk u hC
    rw [hu] at h1
    apply hv0
    have h2 := congrArg (fun m => ((Multiplicative.toAdd m : evenWeight 5) : Fin 5 → ZMod 2)) h1
    simpa using h2
  have hu₁₂ : β (u₁ * u₂) = Multiplicative.ofAdd ⟨v1 + v2, add_mem v1_mem v2_mem⟩ := by
    rw [map_mul, hu₁, hu₂]
    rfl
  refine ⟨x, hxB, hx3, hxC, u₁, u₁.2, u₂, u₂.2, key u₁ v1 v1_mem hu₁ fun i => (hfix i).1,
    key u₂ v2 v2_mem hu₂ fun i => (hfix i).2, hnot u₁ v1 v1_mem hu₁ hv1,
    hnot u₂ v2 v2_mem hu₂ hv2, ?_⟩
  exact hnot (u₁ * u₂) (v1 + v2) (add_mem v1_mem v2_mem) hu₁₂ hv12

variable {X : Subgroup Y} {S : Type} [Group S]

theorem exists_comm_of_map (hBX : B ≤ X) (hS : IsShort2 B) (hA : IsAltType B 5)
    (π : X →* S) (hπ : ∀ g : X, π g = 1 → (g : Y) ∈ Subgroup.centralizer (B : Set Y)) :
    ∃ a b : S, a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 2 = 1 ∧ b ≠ 1 ∧ a * b = b * a := by
  obtain ⟨x, hx, hx3, hxC, w₁, hw₁, -, -, hxw₁, -, hw₁C, -, -⟩ := exists_elements hS hA
  have hw₁B : w₁ ∈ B := C1.blockQ_le B (C1.blockU_le_blockQ hS hw₁)
  refine ⟨π ⟨x, hBX hx⟩, π ⟨w₁, hBX hw₁B⟩, ?_, fun h => hxC (hπ _ h), ?_,
    fun h => hw₁C (hπ _ h), ?_⟩
  · rw [← map_pow]
    have : (⟨x, hBX hx⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  · rw [← map_pow]
    have : (⟨w₁, hBX hw₁B⟩ : X) ^ 2 = 1 := Subtype.ext (by simpa using C1.blockU_sq hS w₁ hw₁)
    rw [this, map_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxw₁

omit [Finite Y] in
theorem card_le_card_map [Finite S] (hBX : B ≤ X) (hS : IsShort2 B) (hA : IsAltType B 5)
    (π : X →* S) (hπ : ∀ g : X, π g = 1 → (g : Y) ∈ Subgroup.centralizer (B : Set Y)) :
    16 ≤ Nat.card (((blockU B).subgroupOf X).map π) := by
  classical
  obtain ⟨-, -, -, β, hβ, hβk, -⟩ := hA
  have hUX : ∀ u : blockU B, (u : Y) ∈ X := fun u =>
    hBX (C1.blockQ_le B (C1.blockU_le_blockQ hS u.2))
  set s := Function.surjInv hβ with hs
  let f : evenWeight 5 → ((blockU B).subgroupOf X).map π := fun v =>
    ⟨π ⟨s (Multiplicative.ofAdd v), hUX _⟩,
      ⟨⟨s (Multiplicative.ofAdd v), hUX _⟩, Subgroup.mem_subgroupOf.mpr (s _).2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro v v' hvv'
    have h1 : π ⟨s (Multiplicative.ofAdd v), hUX _⟩ = π ⟨s (Multiplicative.ofAdd v'), hUX _⟩ :=
      congrArg Subtype.val hvv'
    have h2 : π ((⟨s (Multiplicative.ofAdd v), hUX _⟩ : X)⁻¹ *
        ⟨s (Multiplicative.ofAdd v'), hUX _⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have hC := hπ _ h2
    have h3 := eq_one_of_mem_centralizer β hβk
      ((s (Multiplicative.ofAdd v))⁻¹ * s (Multiplicative.ofAdd v')) hC
    rw [map_mul, map_inv, Function.surjInv_eq hβ, Function.surjInv_eq hβ, inv_mul_eq_one] at h3
    exact Multiplicative.ofAdd.injective h3
  have h := Nat.card_le_card_of_injective f hf
  rwa [AppC.card_evenWeight] at h

omit [Finite Y] in
theorem sixteen_dvd_card [Finite S] (hBX : B ≤ X) (hS : IsShort2 B) (hA : IsAltType B 5)
    (π : X →* S) (hπ : ∀ g : X, π g = 1 → (g : Y) ∈ Subgroup.centralizer (B : Set Y)) :
    16 ∣ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := ((blockU B).subgroupOf X).map π with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hg2 : g ^ 2 = 1 := Subtype.ext (by
      simpa using C1.blockU_sq hS (g : Y) (Subgroup.mem_subgroupOf.mp hg))
    simp [← map_pow, hg2]
  obtain ⟨k, hk⟩ := hMp.exists_card_eq
  have h16 := card_le_card_map hBX hS hA π hπ
  rw [← hM, hk] at h16
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ k := pow_dvd_pow 2 hk4
    _ = Nat.card M := hk.symm
    _ ∣ Nat.card S := Subgroup.card_subgroup_dvd_card M

theorem card_ge (hS : IsShort2 B) (hA : IsAltType B 5) : 960 ≤ Nat.card B := by
  obtain ⟨α, hα, hαk, β, hβ, -, -⟩ := hA
  have h1 : Nat.card B = Nat.card (B ⧸ α.ker) * Nat.card α.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (B ⧸ α.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
    exact A5.Delta5.a5_card
  have h3 : Nat.card α.ker = Nat.card (blockQ B) := by
    rw [hαk]
    show _ = Nat.card ((CFSG.Open.pCore 2 B).map B.subtype)
    rw [Subgroup.card_map_of_injective B.subtype_injective]
  have h4 : Nat.card (blockU B) ≤ Nat.card (blockQ B) :=
    Subgroup.card_le_of_le (C1.blockU_le_blockQ hS)
  have h5 : 16 ≤ Nat.card (blockU B) := by
    have h := Nat.card_le_card_of_surjective β hβ
    rwa [Nat.card_congr Multiplicative.toAdd, AppC.card_evenWeight] at h
  rw [h1, h2, h3]
  omega

end CFSG.Quasithin.H13.KGE623
