module

public import CFSG.Quasithin.H13.A6S13834C
public import CFSG.Quasithin.H13.A6S13834

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

open CFSG.LieType.BorelTits CFSG.Quasithin.F7

@[expose] def preImg {G : Type} [Group G] {H : Subgroup G} (ρ : ↥H →* Perm (Fin 6))
    (X : Subgroup (Perm (Fin 6))) : Subgroup G :=
  (X.comap ρ).map H.subtype

theorem mem_preImg {G : Type} [Group G] {H : Subgroup G} {ρ : ↥H →* Perm (Fin 6)}
    {X : Subgroup (Perm (Fin 6))} {x : G} : x ∈ preImg ρ X ↔ ∃ hx : x ∈ H, ρ ⟨x, hx⟩ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem eq_one_of_two_pow_of_cube {G : Type} [Group G] {x : G} {k : ℕ} (h2 : x ^ (2 ^ k) = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L1_cube : ∃ c ∈ S.L1, c ^ 3 = 1 ∧ c ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hs, h4, h5, h3⟩, -⟩ := three_cycles
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three hs h4 h5 h3
  have h3o : orderOf (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) = 3 :=
    orderOf_eq_prime h3 (by decide)
  have hdvd : 3 ∣ orderOf g := by
    rw [← h3o, ← hg]
    exact orderOf_map_dvd _ _
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < orderOf g := orderOf_pos g
  refine ⟨((g ^ m : ↥(Subgroup.normalizer (V : Set G))) : G), ?_, ?_, ?_⟩
  · simpa using S.L1.pow_mem hgL1 m
  · have h1 : (g ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
    simpa using congrArg Subtype.val h1
  · intro h1
    have h1' : g ^ m = 1 := Subtype.ext (by simpa using h1)
    have hm0 : 0 < m := by omega
    have := orderOf_le_of_pow_eq_one hm0 h1'
    omega

section Coords

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  (hL1H : S.L1 ≤ S.G1)

include hN hL1H in
theorem L1_le_preA4 : S.L1 ≤ preImg ρ a4Sub := by
  change oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hxX, m, hm, hxm⟩
  have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hxX, m, hm, hxm⟩
  have hxH := hL1H hxL1
  refine mem_preImg.2 ⟨hxH, ?_⟩
  have hc : ρ ⟨x, hxH⟩ ∈ cList := (hN _).2 (S.L1T_le_NV3 (Subgroup.mem_sup_left hxL1))
  refine oddOrder_mem_A4 hc hm ?_
  have e : (⟨x, hxH⟩ : ↥S.G1) ^ m = 1 := Subtype.ext (by simpa using hxm)
  rw [← map_pow, e, map_one]

include hker in
theorem rho_ne_one_of_cube {c : ↥S.G1} (h3 : c ^ 3 = 1) (h1 : c ≠ 1) : ρ c ≠ 1 := by
  intro h
  have hQ : (c : G) ∈ pCoreOf 2 S.G1 := (hker c).1 h
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup (r := 2) S.G1 ⟨c, hQ⟩
  have hk' : (c : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  apply h1
  apply Subtype.ext
  exact eq_one_of_two_pow_of_cube hk' (by simpa using congrArg Subtype.val h3)

include hN hker hL1H in
theorem exists_L1_E0 (hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ)) :
    ∀ σ ∈ e0List, ∃ l : ↥S.G1, (l : G) ∈ S.L1 ∧ ρ l = σ := by
  obtain ⟨c, hcL, hc3, hc1⟩ := S.exists_L1_cube
  have hcH := hL1H hcL
  set C : ↥S.G1 := ⟨c, hcH⟩ with hC
  have hC3 : C ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hC1 : C ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hcA : ρ C ∈ a4List := mem_preImg.1 (S.L1_le_preA4 hN hL1H hcL) |>.2
  have hc3' : ρ C ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
  have hc1' : ρ C ≠ 1 := S.rho_ne_one_of_cube hker hC3 hC1
  obtain ⟨t, htT, hnt⟩ : ∃ t : ↥S.G1, (t : G) ∈ T ∧
      ¬ (ρ t * ρ C * (ρ t)⁻¹ = ρ C ∨ ρ t * ρ C * (ρ t)⁻¹ = (ρ C)⁻¹) := by
    by_contra hall
    push Not at hall
    have hle : (T.subgroupOf S.G1).map ρ ≤ normC3 (ρ C) := by
      rintro _ ⟨t, ht, rfl⟩
      have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
      refine ⟨cList_comm _ ((hN t).2 (S.T_le_normalizer_V3 htT)), ?_⟩
      by_contra hn
      push Not at hn
      exact (hall t htT).elim (fun h => hn.1 h) (fun h => hn.2 h) |>.elim
    have h12 := Subgroup.card_dvd_of_le hle
    rw [card_normC3 hcA hc3' hc1'] at h12
    have := hT8.trans h12
    omega
  have htcL : (t : G) * c * (t : G)⁻¹ ∈ S.L1 :=
    (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 htT) c).mp hcL
  set D : ↥S.G1 := t * C * t⁻¹ with hD
  have hDv : ρ D = ρ t * ρ C * (ρ t)⁻¹ := by rw [hD, map_mul, map_mul, map_inv]
  have hDL : (D : G) ∈ S.L1 := htcL
  have hdA : ρ D ∈ a4List := mem_preImg.1 (S.L1_le_preA4 hN hL1H hDL) |>.2
  have hd3 : ρ D ^ 3 = 1 := by
    rw [hDv, show ρ t * ρ C * (ρ t)⁻¹ = MulAut.conj (ρ t) (ρ C) from rfl, ← map_pow, hc3',
      map_one]
  have hd1 : ρ D ≠ 1 := by
    rw [hDv]
    intro h
    apply hc1'
    calc ρ C = (ρ t)⁻¹ * (ρ t * ρ C * (ρ t)⁻¹) * ρ t := by group
      _ = 1 := by rw [h]; group
  rw [not_or] at hnt
  rw [← hDv] at hnt
  obtain ⟨hmem, hall⟩ := E0_of_two_c3 (ρ C) hcA (ρ D) hdA hc3' hc1' hd3 hd1 hnt.1 hnt.2
  have hk : ρ (C * D * C⁻¹ * D⁻¹) = ρ C * ρ D * (ρ C)⁻¹ * (ρ D)⁻¹ := by
    simp only [map_mul, map_inv]
  have hkL : ((C * D * C⁻¹ * D⁻¹ : ↥S.G1) : G) ∈ S.L1 := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact S.L1.mul_mem (S.L1.mul_mem (S.L1.mul_mem hcL hDL) (S.L1.inv_mem hcL)) (S.L1.inv_mem hDL)
  intro σ hσ
  rcases hall σ hσ with h | h | h | h
  · exact ⟨1, S.L1.one_mem, by rw [map_one, h]⟩
  · exact ⟨_, hkL, by rw [hk, h]⟩
  · refine ⟨C * (C * D * C⁻¹ * D⁻¹) * C⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hk, h]⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact S.L1.mul_mem (S.L1.mul_mem hcL hkL) (S.L1.inv_mem hcL)
  · refine ⟨C⁻¹ * (C * D * C⁻¹ * D⁻¹) * C, ?_, by rw [map_mul, map_mul, map_inv, hk, h]⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact S.L1.mul_mem (S.L1.mul_mem (S.L1.inv_mem hcL) hkL) hcL

include hN hker hL1H in
theorem L1Q_le_preA4 : S.L1 ⊔ pCoreOf 2 S.G1 ≤ preImg ρ a4Sub := by
  refine sup_le (S.L1_le_preA4 hN hL1H) fun q hq => ?_
  refine mem_preImg.2 ⟨pCoreOf_le 2 S.G1 hq, ?_⟩
  rw [(hker _).2 hq]
  exact a4Sub.one_mem

include hN hker hL1H in
theorem mem_O2_of_E0 {l : ↥S.G1} (hl : (l : G) ∈ S.L1 ⊔ pCoreOf 2 S.G1) (he : ρ l ∈ e0List) :
    (l : G) ∈ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) := by
  set Q := pCoreOf 2 S.G1 with hQ
  have hA := S.L1Q_le_preA4 hN hker hL1H
  set P : Subgroup G := preImg ρ e0Sub ⊓ (S.L1 ⊔ Q) with hP
  have fwd : ∀ y ∈ S.L1 ⊔ Q, ∀ x ∈ P, y * x * y⁻¹ ∈ P := by
    intro y hy x hx
    obtain ⟨hxH, hxE⟩ := mem_preImg.1 hx.1
    obtain ⟨hyH, hyA⟩ := mem_preImg.1 (hA hy)
    refine ⟨mem_preImg.2 ⟨S.G1.mul_mem (S.G1.mul_mem hyH hxH) (S.G1.inv_mem hyH), ?_⟩,
      (S.L1 ⊔ Q).mul_mem ((S.L1 ⊔ Q).mul_mem hy hx.2) ((S.L1 ⊔ Q).inv_mem hy)⟩
    have e : (⟨y * x * y⁻¹, S.G1.mul_mem (S.G1.mul_mem hyH hxH) (S.G1.inv_mem hyH)⟩ : ↥S.G1) =
        ⟨y, hyH⟩ * ⟨x, hxH⟩ * (⟨y, hyH⟩ : ↥S.G1)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact a4_normal_e0 _ hyA _ hxE
  have hnorm : S.L1 ⊔ Q ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fwd y hy x, fun hx => ?_⟩
    have := fwd y⁻¹ ((S.L1 ⊔ Q).inv_mem hy) _ hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this
  have hp : IsPGroup 2 P := by
    rintro ⟨x, hx⟩
    obtain ⟨hxH, hxE⟩ := mem_preImg.1 hx.1
    have hsq : ρ (⟨x, hxH⟩ ^ 2 : ↥S.G1) = 1 := by rw [map_pow, pow_two]; exact e0_sq _ hxE
    have hxQ := (hker _).1 hsq
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup (r := 2) S.G1 ⟨_, hxQ⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (x ^ 2) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, hk']
  have hle : P ≤ pCoreOf 2 (S.L1 ⊔ Q) := le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hp
  exact hle ⟨mem_preImg.2 ⟨l.2, he⟩, hl⟩

end Coords

end Setting4

theorem quad_identity {G : Type} [Group G] {B X : Subgroup G}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBX : ∀ b ∈ B, ∀ y ∈ X, b * y * b⁻¹ * y⁻¹ ∈ B)
    {b₁ b₂ y : G} (h1 : b₁ ∈ B) (h2 : b₂ ∈ B) (hy : y ∈ X) :
    (b₂ * b₁) * y * (b₂ * b₁)⁻¹ * (b₂ * y * b₂⁻¹)⁻¹ = b₁ * y * b₁⁻¹ * y⁻¹ := by
  have hc := hBc b₂ h2 _ (hBX b₁ h1 y hy)
  calc (b₂ * b₁) * y * (b₂ * b₁)⁻¹ * (b₂ * y * b₂⁻¹)⁻¹ =
        b₂ * (b₁ * y * b₁⁻¹ * y⁻¹) * b₂⁻¹ := by group
    _ = (b₁ * y * b₁⁻¹ * y⁻¹) * b₂ * b₂⁻¹ := by rw [hc]
    _ = b₁ * y * b₁⁻¹ * y⁻¹ := by group

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Quad

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀3 : v₀ ∉ S.V3)
include hN h13315 hv₀ hv₀3

theorem point_congr {k k' : ↥S.G1} (h : ρ k⁻¹ * ρ k' ∈ cList) :
    ((k : G) * v₀ * (k : G)⁻¹)⁻¹ * ((k' : G) * v₀ * (k' : G)⁻¹) ∈ conjClosure S.V3 S.G1 := by
  have hg3 : ((k⁻¹ * k' : ↥S.G1) : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    (hN _).1 (by rw [map_mul]; exact h)
  have hgV := S.G1_inf_G3_le h13315 ⟨(k⁻¹ * k').2, hg3⟩
  set g : G := ((k⁻¹ * k' : ↥S.G1) : G) with hg
  have hgv : g * v₀ * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV v₀).mp hv₀
  have hgv3 : g * v₀ * g⁻¹ ∉ S.V3 := fun h' =>
    hv₀3 ((Subgroup.mem_normalizer_iff.mp hg3 v₀).mpr h')
  have hw : v₀⁻¹ * (g * v₀ * g⁻¹) ∈ S.V3 :=
    inv_mul_mem_of_relIndex_two S.relIndex_V3_V hv₀ hgv hv₀3 hgv3
  have e : ((k : G) * v₀ * (k : G)⁻¹)⁻¹ * ((k' : G) * v₀ * (k' : G)⁻¹) =
      (k : G) * (v₀⁻¹ * (g * v₀ * g⁻¹)) * (k : G)⁻¹ := by
    rw [hg]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  rw [e]
  exact mem_conjClosure k.2 hw

theorem fix_of_cert (hVH : IsElemAbelian 2 (conjClosure V S.G1)) (hVab : IsElemAbelian 2 V)
    {B : Subgroup G} (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBV : ∀ b ∈ B, ∀ y ∈ conjClosure V S.G1, b * y * b⁻¹ * y⁻¹ ∈ B)
    {x b₁ b₂ : ↥S.G1} (hb₁ : (b₁ : G) ∈ B) (hb₂ : (b₂ : G) ∈ B)
    (hx : ρ x = swap 1 2 * swap 3 4) (he₁ : ρ b₁ = swap 0 1 * swap 2 3)
    (he₂ : ρ b₂ = swap 0 1 * swap 4 5) :
    (x : G) * v₀ * (x : G)⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  have : IsMulCommutative ↥(conjClosure V S.G1) := hVH.1
  have hp : ∀ k : ↥S.G1, (k : G) * v₀ * (k : G)⁻¹ ∈ conjClosure V S.G1 := fun k =>
    mem_conjClosure k.2 hv₀
  let U' : Subgroup ↥(conjClosure V S.G1) :=
    (conjClosure S.V3 S.G1).subgroupOf (conjClosure V S.G1)
  let f : ↥S.G1 → ↥(conjClosure V S.G1) ⧸ U' := fun k =>
    QuotientGroup.mk (⟨_, hp k⟩ : ↥(conjClosure V S.G1))
  have fcong : ∀ k k' : ↥S.G1, ρ k⁻¹ * ρ k' ∈ cList → f k = f k' := by
    intro k k' h
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    exact S.point_congr hN h13315 hv₀ hv₀3 h
  have hv2 : v₀ ^ 2 = 1 := isElemAbelian_pow_eq_one hVab hv₀
  have fsq : ∀ k, f k * f k = 1 := by
    intro k
    rw [← QuotientGroup.mk_mul]
    have e : (⟨_, hp k⟩ : ↥(conjClosure V S.G1)) * ⟨_, hp k⟩ = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, OneMemClass.coe_one]
      calc (k : G) * v₀ * (k : G)⁻¹ * ((k : G) * v₀ * (k : G)⁻¹) =
          (k : G) * (v₀ * v₀) * (k : G)⁻¹ := by group
        _ = 1 := by rw [← pow_two, hv2]; group
    rw [e, QuotientGroup.mk_one]
  have fcomm : ∀ k k', f k * f k' = f k' * f k := by
    intro k k'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mul_comm' (⟨_, hp k⟩ : ↥(conjClosure V S.G1))]
  have toW : ∀ a b c d : ↥S.G1,
      ((a : G) * v₀ * (a : G)⁻¹) * ((b : G) * v₀ * (b : G)⁻¹)⁻¹ =
        ((c : G) * v₀ * (c : G)⁻¹) * ((d : G) * v₀ * (d : G)⁻¹)⁻¹ →
      f a * (f b)⁻¹ = f c * (f d)⁻¹ := by
    intro a b c d h
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h
  have hb₁H := b₁.2
  have E1 : f (b₂ * b₁ * x) * (f (b₂ * x))⁻¹ = f (b₁ * x) * (f x)⁻¹ := by
    refine toW _ _ _ _ ?_
    have q := quad_identity hBc hBV hb₁ hb₂ (hp x)
    simp only [Subgroup.coe_mul]
    calc (b₂ : G) * b₁ * x * v₀ * ((b₂ : G) * b₁ * x)⁻¹ * ((b₂ : G) * x * v₀ * ((b₂ : G) * x)⁻¹)⁻¹
        = ((b₂ : G) * b₁) * ((x : G) * v₀ * (x : G)⁻¹) * ((b₂ : G) * b₁)⁻¹ *
            ((b₂ : G) * ((x : G) * v₀ * (x : G)⁻¹) * (b₂ : G)⁻¹)⁻¹ := by group
      _ = (b₁ : G) * ((x : G) * v₀ * (x : G)⁻¹) * (b₁ : G)⁻¹ * ((x : G) * v₀ * (x : G)⁻¹)⁻¹ := q
      _ = (b₁ : G) * x * v₀ * ((b₁ : G) * x)⁻¹ * ((x : G) * v₀ * (x : G)⁻¹)⁻¹ := by group
  have E2 : f (x * b₂ * b₁ * x⁻¹) * (f (x * b₂ * x⁻¹))⁻¹ = f (x * b₁ * x⁻¹) * (f 1)⁻¹ := by
    refine toW _ _ _ _ ?_
    have q := quad_identity hBc hBV hb₁ hb₂ (hp x⁻¹)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one] at q ⊢
    calc (x : G) * b₂ * b₁ * (x : G)⁻¹ * v₀ * ((x : G) * b₂ * b₁ * (x : G)⁻¹)⁻¹ *
          ((x : G) * b₂ * (x : G)⁻¹ * v₀ * ((x : G) * b₂ * (x : G)⁻¹)⁻¹)⁻¹
        = (x : G) * (((b₂ : G) * b₁) * ((x : G)⁻¹ * v₀ * (x : G)⁻¹⁻¹) * ((b₂ : G) * b₁)⁻¹ *
            ((b₂ : G) * ((x : G)⁻¹ * v₀ * (x : G)⁻¹⁻¹) * (b₂ : G)⁻¹)⁻¹) * (x : G)⁻¹ := by group
      _ = (x : G) * ((b₁ : G) * ((x : G)⁻¹ * v₀ * (x : G)⁻¹⁻¹) * (b₁ : G)⁻¹ *
            ((x : G)⁻¹ * v₀ * (x : G)⁻¹⁻¹)⁻¹) * (x : G)⁻¹ := by rw [q]
      _ = (x : G) * b₁ * (x : G)⁻¹ * v₀ * ((x : G) * b₁ * (x : G)⁻¹)⁻¹ * (1 * v₀ * 1⁻¹)⁻¹ := by
          group
  have C1 : f (b₂ * b₁ * x) = f (x * b₁ * x⁻¹) := fcong _ _ (by
    simp only [map_mul, map_inv, hx, he₁, he₂]
    exact cert_pts.2.2.2.2.1)
  have C2 : f (b₂ * x) = f (x * b₂ * x⁻¹) := fcong _ _ (by
    simp only [map_mul, map_inv, hx, he₂]
    exact cert_pts.2.2.2.2.2.1)
  have C3 : f (b₁ * x) = f (x * b₂ * b₁ * x⁻¹) := fcong _ _ (by
    simp only [map_mul, map_inv, hx, he₁, he₂]
    exact cert_pts.2.2.2.2.2.2)
  rw [C1, C2, C3] at E1
  have hai := inv_eq_of_mul_eq_one_right (fsq (x * b₁ * x⁻¹))
  have hci := inv_eq_of_mul_eq_one_right (fsq (x * b₂ * b₁ * x⁻¹))
  have hac := fcomm (x * b₂ * b₁ * x⁻¹) (x * b₁ * x⁻¹)
  have key : f x = f 1 := by
    generalize f (x * b₁ * x⁻¹) = a at E1 E2 hai hac
    generalize f (x * b₂ * x⁻¹) = bb at E1 E2
    generalize f (x * b₂ * b₁ * x⁻¹) = c at E1 E2 hci hac
    generalize f x = d at E1 ⊢
    generalize f 1 = e at E2 ⊢
    have hd : d⁻¹ = c⁻¹ * (a * bb⁻¹) := by rw [E1]; group
    have he : e⁻¹ = a⁻¹ * (c * bb⁻¹) := by rw [E2]; group
    have : d⁻¹ = e⁻¹ := by rw [hd, he, hai, hci, ← mul_assoc, ← mul_assoc, hac]
    exact inv_injective this
  have hmem := QuotientGroup.eq.1 key
  rw [Subgroup.mem_subgroupOf] at hmem
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one] at hmem
  rw [one_mul, inv_one, mul_one] at hmem
  set y := (x : G) * v₀ * (x : G)⁻¹ with hy
  have hyv : y * v₀ = v₀ * y := isElemAbelian_comm hVH (hp x) (le_conjClosure V S.G1 hv₀)
  have e : y * v₀⁻¹ = (y⁻¹ * v₀)⁻¹ := by
    calc y * v₀⁻¹ = v₀⁻¹ * (v₀ * y) * v₀⁻¹ := by group
      _ = v₀⁻¹ * (y * v₀) * v₀⁻¹ := by rw [hyv]
      _ = (y⁻¹ * v₀)⁻¹ := by group
  rw [e]
  exact (conjClosure S.V3 S.G1).inv_mem hmem

end Quad

end Setting4

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Fix

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hN : ∀ g : ↥S.G1, ρ g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  (h13315 : Stmt13_3_15) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀3 : v₀ ∉ S.V3)

include h13315 hv₀ hv₀3 in
theorem comm_mem_of_normalizer {g : G} (hgH : g ∈ S.G1)
    (hg3 : g ∈ Subgroup.normalizer (S.V3 : Set G)) :
    g * v₀ * g⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  have hgV := S.G1_inf_G3_le h13315 ⟨hgH, hg3⟩
  have hgv : g * v₀ * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV v₀).mp hv₀
  have hgv3 : g * v₀ * g⁻¹ ∉ S.V3 := fun h' =>
    hv₀3 ((Subgroup.mem_normalizer_iff.mp hg3 v₀).mpr h')
  have hw := inv_mul_mem_of_relIndex_two S.relIndex_V3_V (V.inv_mem hgv) (V.inv_mem hv₀)
    (fun h' => hgv3 (S.V3.inv_mem_iff.mp h')) (fun h' => hv₀3 (S.V3.inv_mem_iff.mp h'))
  rw [inv_inv] at hw
  exact le_conjClosure S.V3 S.G1 hw

include hN h13315 hv₀ hv₀3 in
theorem fix_all {K : Subgroup G} (hKT : K ⊔ T = S.G1)
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) (hQT : pCoreOf 2 S.G1 ≤ T)
    {x : ↥S.G1} (hx : ρ x = swap 1 2 * swap 3 4)
    (hxv : (x : G) * v₀ * (x : G)⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1) :
    ∀ h ∈ S.G1, h * v₀ * h⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1 := by
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ k ∈ S.G1, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hk) u).mp hu
  let Fix : Subgroup G :=
    { carrier := {h | h ∈ S.G1 ∧ h * v₀ * h⁻¹ * v₀⁻¹ ∈ U}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨S.G1.mul_mem ha hb, ?_⟩
        have e : a * b * v₀ * (a * b)⁻¹ * v₀⁻¹ =
            (a * (b * v₀ * b⁻¹ * v₀⁻¹) * a⁻¹) * (a * v₀ * a⁻¹ * v₀⁻¹) := by group
        rw [e]
        exact U.mul_mem (hUN a ha _ hb') ha'
      one_mem' := ⟨S.G1.one_mem, by rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact U.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨S.G1.inv_mem ha, ?_⟩
        have e : a⁻¹ * v₀ * a⁻¹⁻¹ * v₀⁻¹ = a⁻¹ * (a * v₀ * a⁻¹ * v₀⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hUN _ (S.G1.inv_mem ha) _ (U.inv_mem ha') }
  have hmemFix : ∀ h, h ∈ Fix ↔ h ∈ S.G1 ∧ h * v₀ * h⁻¹ * v₀⁻¹ ∈ U := fun h => Iff.rfl
  have hNfix : ∀ g : ↥S.G1, (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) → (g : G) ∈ Fix :=
    fun g hg => (hmemFix _).2 ⟨g.2, S.comm_mem_of_normalizer h13315 hv₀ hv₀3 g.2 hg⟩
  set X := (Fix.subgroupOf S.G1).map ρ with hX
  have hCX : cA6 ≤ X := by
    intro σ hσ
    obtain ⟨k, -, hk⟩ := honto σ (Equiv.Perm.mem_alternatingGroup.mpr hσ.2)
    refine ⟨k, Subgroup.mem_subgroupOf.mpr (hNfix k ((hN k).1 ?_)), hk⟩
    rw [hk]
    exact mem_cList σ hσ.1
  have hsX : swap 1 2 * swap 3 4 ∈ X :=
    ⟨x, Subgroup.mem_subgroupOf.mpr ((hmemFix _).2 ⟨x.2, hxv⟩), hx⟩
  have hA6 := alt6_le_of_overgroup hCX hsX cert_pts.1 cert_pts.2.1
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  have hTFix : T ≤ Fix := fun t ht =>
    hNfix ⟨t, hTH ht⟩ (S.T_le_normalizer_V3 ht)
  have hKFix : K ≤ Fix := by
    intro k hk
    have hkH : k ∈ S.G1 := hKT ▸ Subgroup.mem_sup_left hk
    obtain ⟨f, hf, hfk⟩ := hA6 (hKA ⟨k, hkH⟩ hk)
    have hfF : (f : G) ∈ Fix := Subgroup.mem_subgroupOf.mp hf
    have h1 : ρ (f⁻¹ * ⟨k, hkH⟩) = 1 := by rw [map_mul, map_inv, hfk, inv_mul_cancel]
    have hQ := (hker _).1 h1
    have hF2 : ((f⁻¹ * ⟨k, hkH⟩ : ↥S.G1) : G) ∈ Fix := hTFix (hQT hQ)
    have e : k = (f : G) * ((f⁻¹ * ⟨k, hkH⟩ : ↥S.G1) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact Fix.mul_mem hfF hF2
  have hall : S.G1 ≤ Fix := hKT ▸ sup_le hKFix hTFix
  exact fun h hh => ((hmemFix h).1 (hall hh)).2

include h13315 hv₀ hv₀3 in
theorem false_of_fix (hNS : ¬ LieModel G .PSp 3 2 1)
    (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14) (hVle : V ≤ S.G1)
    (hall : ∀ h ∈ S.G1, h * v₀ * h⁻¹ * v₀⁻¹ ∈ conjClosure S.V3 S.G1) : False := by
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ k ∈ S.G1, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hk) u).mp hu
  have hV : ∀ h ∈ S.G1, ∀ y ∈ V, h * y * h⁻¹ * y⁻¹ ∈ U := by
    intro h hh y hy
    by_cases hy3 : y ∈ S.V3
    · exact U.mul_mem (mem_conjClosure hh hy3) (U.inv_mem (le_conjClosure S.V3 S.G1 hy3))
    · have hw := inv_mul_mem_of_relIndex_two S.relIndex_V3_V (V.inv_mem hy) (V.inv_mem hv₀)
        (fun h' => hy3 (S.V3.inv_mem_iff.mp h')) (fun h' => hv₀3 (S.V3.inv_mem_iff.mp h'))
      rw [inv_inv] at hw
      have e : h * y * h⁻¹ * y⁻¹ =
          (h * (y * v₀⁻¹) * h⁻¹) * (h * v₀ * h⁻¹ * v₀⁻¹) * (y * v₀⁻¹)⁻¹ := by group
      rw [e]
      exact U.mul_mem (U.mul_mem (mem_conjClosure hh hw) (hall h hh))
        (U.inv_mem (le_conjClosure S.V3 S.G1 hw))
  let Z : Subgroup G :=
    { carrier := {z | z ∈ S.G1 ∧ ∀ h ∈ S.G1, h * z * h⁻¹ * z⁻¹ ∈ U}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨S.G1.mul_mem ha hb, fun h hh => ?_⟩
        have e : h * (a * b) * h⁻¹ * (a * b)⁻¹ =
            (h * a * h⁻¹ * a⁻¹) * (a * (h * b * h⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact U.mul_mem (ha' h hh) (hUN a ha _ (hb' h hh))
      one_mem' := ⟨S.G1.one_mem, fun h _ => by
        rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact U.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨S.G1.inv_mem ha, fun h hh => ?_⟩
        have e : h * a⁻¹ * h⁻¹ * a⁻¹⁻¹ = a⁻¹ * (h * a * h⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := hUN a⁻¹ (S.G1.inv_mem ha) _ (U.inv_mem (ha' h hh))
        rwa [inv_inv] at this }
  have hVZ : conjClosure V S.G1 ≤ Z := by
    refine conjClosure_le fun k hk y hy => ⟨S.G1.mul_mem (S.G1.mul_mem hk (hVle hy))
      (S.G1.inv_mem hk), fun h hh => ?_⟩
    have e : h * (k * y * k⁻¹) * h⁻¹ * (k * y * k⁻¹)⁻¹ =
        ((h * k) * y * (h * k)⁻¹ * y⁻¹) * (k * y * k⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact U.mul_mem (hV _ (S.G1.mul_mem hh hk) y hy) (U.inv_mem (hV k hk y hy))
  exact S.not_comm_VH_H_le_UH hNS h13315 h1356two hG1 h13314 fun h hh z hz => (hVZ hz).2 h hh

end Fix

end Setting4

open scoped commutatorElement

theorem dvd_four_of_dvd_eight : ∀ n : Fin 9, 0 < n.val → n.val ∣ 8 → n.val ≠ 8 → n.val ∣ 2 ^ 2 := by
  decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem lemma13_8_34_three (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (h13314 : Stmt13_3_14) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K) (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hβ : UHCoords S ρ) {c : G} (hc : c ∈ S.G1)
    (hcV : conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T)) :
    ¬ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) ≤ conjSub c (F8.Uγ V S.G1 (g : G)) ⊔ pCoreOf 2 S.G1 ∧
      mIdx (F8.Uγ V S.G1 (g : G)) (F8.Uγ V S.G1 (g : G) ⊓ pCoreOf 2 S.G1) ≤ 2 := by
  set Q := pCoreOf 2 S.G1 with hQdef
  set Vγ := F8.Uγ V S.G1 (g : G) with hVγdef
  have hL1H : S.L1 ≤ S.G1 := hL1K.trans (hKT ▸ le_sup_left)
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  have hQT : Q ≤ T := isSylowTwoOf_pCoreOf_le hF.toHypF91.sylow_H
  have hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ) :=
    eight_dvd_card_map hF.toHypF91.sylow_H ρ (fun h h1 => hQT ((hker h).1 h1))
      fun σ hσ => (honto σ hσ).elim fun k hk => ⟨k, hk.2⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 6), ∀ g : ↥S.G1,
      τ⁻¹ * ρ g * τ ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
    rcases hβ with ⟨β, -, hβk, hβe⟩ | ⟨β, -, hβk, hβe⟩
    · exact S.exists_tau_nat hβk hβe hT8
    · exact S.exists_tau_cover hβk hβe (sup_le hL1H hTH) hT8
  set ρ' : ↥S.G1 →* Perm (Fin 6) := (MulAut.conj τ⁻¹).toMonoidHom.comp ρ with hρ'def
  have hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ := fun g => by
    simp only [hρ'def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
  have hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    fun g => by rw [hρ']; exact hτ g
  have hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ Q := by
    intro h
    rw [hρ', ← hker h]
    constructor
    · intro e
      calc ρ h = τ * (τ⁻¹ * ρ h * τ) * τ⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e
      rw [e]; group
  have hAn := (alternatingGroup.normal : (alternatingGroup (Fin 6)).Normal)
  have hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6) := fun k hk => by
    rw [hρ']
    have := hAn.conj_mem _ (hKA k hk) τ⁻¹
    rwa [inv_inv] at this
  have honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ := by
    intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := honto _ (hAn.conj_mem σ hσ τ)
    exact ⟨k, hk, by rw [hρ', hkσ]; group⟩
  have hT8' : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ') :=
    eight_dvd_card_map hF.toHypF91.sylow_H ρ' (fun h h1 => hQT ((hker' h).1 h1))
      fun σ hσ => (honto' σ hσ).elim fun k hk => ⟨k, hk.2⟩
  set B := conjSub c Vγ with hBdef
  have hBH : B ≤ S.G1 := by
    intro b hb
    have h1 := hF.Vγ_le_H s (mem_conjSub.mp hb)
    have e : b = c * (c⁻¹ * b * c) * c⁻¹ := by group
    rw [e]
    exact S.G1.mul_mem (S.G1.mul_mem hc h1) (S.G1.inv_mem hc)
  have hBab : IsElemAbelian 2 B := isElemAbelian_conjSub hF.isElemAbelian_Vγ
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => isElemAbelian_comm hBab ha hb
  have hBV : ∀ b ∈ B, ∀ y ∈ conjClosure V S.G1, b * y * b⁻¹ * y⁻¹ ∈ B := by
    have h3 := hF.F913_3 s (X := V) (Y := V) (Or.inr rfl) (Or.inr rfl)
    intro b hb y hy
    have hb' : c⁻¹ * b * c ∈ Vγ := mem_conjSub.mp hb
    have hy' : c⁻¹ * y * c ∈ conjClosure V S.G1 := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure V S.G1 (S.G1.inv_mem hc)) y).mp hy
      rwa [inv_inv] at this
    have hcomm : ⁅c⁻¹ * y * c, c⁻¹ * b * c⁆ ∈ Vγ :=
      (h3 (Subgroup.commutator_mem_commutator hy' hb')).2
    have e : b * y * b⁻¹ * y⁻¹ = c * ⁅c⁻¹ * y * c, c⁻¹ * b * c⁆⁻¹ * c⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem_conjSub (Vγ.inv_mem hcomm)
  have h3a : ¬ pCoreOf 2 (S.L1 ⊔ Q) ≤ B ⊔ Q := by
    intro hcon
    obtain ⟨l₁, hl₁, he₁⟩ := S.exists_L1_E0 hN' hker' hL1H hT8' _ cert_pts.2.2.1
    obtain ⟨l₂, hl₂, he₂⟩ := S.exists_L1_E0 hN' hker' hL1H hT8' _ cert_pts.2.2.2.1
    have hO₁ := S.mem_O2_of_E0 hN' hker' hL1H (Subgroup.mem_sup_left hl₁)
      (by rw [he₁]; exact cert_pts.2.2.1)
    have hO₂ := S.mem_O2_of_E0 hN' hker' hL1H (Subgroup.mem_sup_left hl₂)
      (by rw [he₂]; exact cert_pts.2.2.2.1)
    have himg : ∀ l : ↥S.G1, (l : G) ∈ B ⊔ Q → ∃ b : ↥S.G1, (b : G) ∈ B ∧ ρ' b = ρ' l := by
      intro l hl
      have hle : B ⊔ Q ≤ preImg ρ' ((B.subgroupOf S.G1).map ρ') := by
        refine sup_le (fun b hb => mem_preImg.2 ⟨hBH hb,
          ⟨⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩⟩) fun q hq =>
          mem_preImg.2 ⟨pCoreOf_le 2 S.G1 hq, ?_⟩
        rw [(hker' _).2 hq]
        exact Subgroup.one_mem _
      obtain ⟨_, ⟨b, hb, hbl⟩⟩ := mem_preImg.1 (hle hl)
      exact ⟨b, Subgroup.mem_subgroupOf.mp hb, hbl⟩
    obtain ⟨b₁, hb₁, hb₁e⟩ := himg l₁ (hcon hO₁)
    obtain ⟨b₂, hb₂, hb₂e⟩ := himg l₂ (hcon hO₂)
    obtain ⟨x, -, hx⟩ := honto' _ (Equiv.Perm.mem_alternatingGroup.mpr cert_pts.1)
    obtain ⟨v₀, hv₀, hv₀3⟩ : ∃ v₀ ∈ V, v₀ ∉ S.V3 := by
      by_contra h
      push Not at h
      have h1 := Subgroup.relIndex_eq_one.mpr (show V ≤ S.V3 from h)
      rw [S.relIndex_V3_V] at h1
      exact absurd h1 (by norm_num)
    have hxv := S.fix_of_cert hN' h13315 hv₀ hv₀3 hF.F911_2 hF.toHypF91.elemAbelian hBc hBV
      hb₁ hb₂ hx (by rw [hb₁e, he₁]) (by rw [hb₂e, he₂])
    have hall := S.fix_all hN' h13315 hv₀ hv₀3 hKT honto' hKA' hker' hQT hx hxv
    exact S.false_of_fix h13315 hv₀ hv₀3 hNS h1356two hG1 h13314 hF.toHypF91.V_le_H hall
  refine ⟨h3a, ?_⟩
  have h2el : ∀ z : ↥S.G1, (z : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' z ^ 4 = 1 := by
    intro z hz
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup (r := 2) (S.L1 ⊔ T) ⟨z, hz⟩
    have hk' : z ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    refine pow_four_of_two ((hN' z).2 (S.L1T_le_NV3 (pCoreOf_le 2 _ hz))) (k := k) ?_
    rw [← map_pow, hk', map_one]
  have hE8 : ∀ y : ↥S.G1, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' y ∈ e8List := by
    intro y hy
    obtain ⟨c₀, hc₀L, hc₀3, hc₀1⟩ := S.exists_L1_cube
    set C : ↥S.G1 := ⟨c₀, hL1H hc₀L⟩ with hC
    have hC3 : C ^ 3 = 1 := Subtype.ext (by simpa using hc₀3)
    have hC1 : C ≠ 1 := fun h => hc₀1 (congrArg Subtype.val h)
    have hCA : ρ' C ∈ a4List := (mem_preImg.1 (S.L1_le_preA4 hN' hL1H hc₀L)).2
    have hC3' : ρ' C ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
    have hC1' : ρ' C ≠ 1 := S.rho_ne_one_of_cube hker' hC3 hC1
    have hyc : ρ' y ∈ cList := (hN' y).2 (S.L1T_le_NV3 (pCoreOf_le 2 _ hy))
    by_contra hne
    have hcy : ((C * y * C⁻¹ : ↥S.G1) : G) ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) (Subgroup.mem_sup_left hc₀L)) y).mp hy
    have hprod : ((y * (C * y * C⁻¹) : ↥S.G1) : G) ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hy hcy
    have h4 := h2el _ hprod
    rw [map_mul, map_mul, map_mul, map_inv] at h4
    exact mem_E8_of_c3 _ hCA hC3' hC1' _ hyc (h2el y hy) hne h4
  let fB : ↥B →* Perm (Fin 6) := ρ'.comp (Subgroup.inclusion hBH)
  have hrange : fB.range ≤ e8Sub := by
    rintro _ ⟨b, rfl⟩
    exact hE8 _ (hcV b.2)
  have hdvd : Nat.card fB.range ∣ 8 := card_e8Sub ▸ Subgroup.card_dvd_of_le hrange
  have hne8 : Nat.card fB.range ≠ 8 := by
    intro h8
    have heq : fB.range = e8Sub := Subgroup.eq_of_le_of_card_ge hrange (by rw [h8, card_e8Sub])
    apply h3a
    intro y hy
    have hyL : y ∈ S.L1 ⊔ Q := pCoreOf_le 2 _ hy
    obtain ⟨hyH, hyA⟩ := mem_preImg.1 (S.L1Q_le_preA4 hN' hker' hL1H hyL)
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup (r := 2) (S.L1 ⊔ Q) ⟨y, hy⟩
    have hk' : (⟨y, hyH⟩ : ↥S.G1) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hyE0 : ρ' ⟨y, hyH⟩ ∈ e0List := mem_e0_of_two hyA (k := k) (by rw [← map_pow, hk', map_one])
    have hyR : ρ' ⟨y, hyH⟩ ∈ fB.range := by
      rw [heq]
      exact e0_sub_e8 _ hyE0
    obtain ⟨b, hb⟩ := hyR
    have hbQ : (((Subgroup.inclusion hBH b)⁻¹ * ⟨y, hyH⟩ : ↥S.G1) : G) ∈ Q := by
      refine (hker' _).1 ?_
      rw [map_mul, map_inv]
      have : ρ' (Subgroup.inclusion hBH b) = ρ' ⟨y, hyH⟩ := hb
      rw [this, inv_mul_cancel]
    have e : y = (b : G) * (((Subgroup.inclusion hBH b)⁻¹ * ⟨y, hyH⟩ : ↥S.G1) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Subgroup.coe_inclusion]
      group
    rw [e]
    exact (B ⊔ Q).mul_mem (Subgroup.mem_sup_left b.2) (Subgroup.mem_sup_right hbQ)
  have hidx : (Vγ ⊓ Q).relIndex Vγ = Nat.card fB.range := by
    have e1 : (B ⊓ Q).relIndex B = (Vγ ⊓ Q).relIndex Vγ := by
      have : B ⊓ Q = conjSub c (Vγ ⊓ Q) := by
        rw [conjSub_inf, F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 S.G1 hc)]
      rw [this]
      exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective
    rw [← e1, Subgroup.inf_relIndex_left]
    have hk : fB.ker = Q.subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hker' _
    rw [Subgroup.relIndex, ← hk, Subgroup.index_ker]
  unfold mIdx
  rw [hidx]
  have hpos : 0 < Nat.card fB.range := Nat.card_pos
  have hle8 : Nat.card fB.range ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : Nat.card fB.range ∣ 2 ^ 2 :=
    dvd_four_of_dvd_eight ⟨Nat.card fB.range, by omega⟩ hpos hdvd hne8
  have hv : 2 ^ padicValNat 2 (Nat.card fB.range) ∣ 2 ^ 2 := pow_padicValNat_dvd.trans h4
  exact (pow_dvd_pow_iff (by norm_num) (by simp)).mp hv

end Setting4

@[expose] def Lemma13834SixOneTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → ∀ hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1,
      S.Struct13827 → ¬ IsHatA6 L →
      (∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) < F8.Uγ S.V3 S.G1 (g : G)) →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        0 < mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) →
        mIdx (conjClosure S.V3 S.G1) (F8.DH S.V3 (fsuV1 T V) S.G1 (g : G)) ≤
          mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) →
        autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 S.G1 (g : G)))
            (tildeOf (fsuV1 T V) (conjClosure S.V3 S.G1)) ∈
          @Qset ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 S.G1))
            (commGroupOfElemAbelian hF.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf (fsuV1 T V) S.G1) (tildeOf (fsuV1 T V) (conjClosure S.V3 S.G1))) →
        ∀ c ∈ S.G1, conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T) →
          (F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1 ∧
            fsuV1 T V ≤ F8.Uγ S.V3 S.G1 (g : G)) ∧
          mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) = 1

theorem lemma13834Six_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (h12 : Lemma13834SixOneTwo) :
    Lemma13834Six := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat hlt γ γ' g s hpos hle hQ c hc hcV
  obtain ⟨h1, h2⟩ :=
    h12 G T L V S hNS hNU hG1 hab hF hst hhat hlt γ γ' g s hpos hle hQ c hc hcV
  obtain ⟨K, -, hKT, hL1K, -, hcase, -⟩ := hst
  rcases hcase with ⟨-, ρ, hker, hKA, honto, hβ⟩ | ⟨hh, -⟩
  · obtain ⟨h3a, h3b⟩ := S.lemma13_8_34_three hNS h13315 h1356two hG1 h13314 hF s hKT hL1K ρ
      hker hKA honto hβ hc hcV
    exact ⟨h1, h2, h3a, h3b⟩
  · exact absurd hh hhat

end CFSG.Quasithin.H13.A6
