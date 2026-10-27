module

public import CFSG.Quasithin.H13.A6S1372L76S

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix
open scoped IsMulCommutative

namespace A6L76T

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

@[expose] noncomputable def mat7 (σ : (FFModel.a7Four α).Gam) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ((α (altLift7 σ) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))

@[expose] noncomputable def vec7 (q : ↥(FFModel.a7Four α).sec ⧸
    (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) : Fin 4 → ZMod 2 :=
  Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from
    (QuotientGroup.mk_surjective q).choose.1)

theorem vec7_mk (m : ↥(FFModel.a7Four α).sec) :
    vec7 α (QuotientGroup.mk m) =
      Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from m.1) := by
  rw [vec7, A6L76R.mk_inj_a7 (QuotientGroup.mk_surjective (QuotientGroup.mk m :
    ↥(FFModel.a7Four α).sec ⧸ (FFModel.a7Four α).ker.subgroupOf
      (FFModel.a7Four α).sec)).choose_spec]

theorem vec7_injective : Function.Injective (vec7 α) := by
  intro q q' h
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m', rfl⟩ := QuotientGroup.mk_surjective q'
  rw [vec7_mk, vec7_mk] at h
  exact congrArg _ (Subtype.ext (Multiplicative.toAdd.injective h))

theorem vec7_mul (q q' : ↥(FFModel.a7Four α).sec ⧸
    (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) :
    vec7 α (q * q') = vec7 α q + vec7 α q' := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m', rfl⟩ := QuotientGroup.mk_surjective q'
  rw [← QuotientGroup.mk_mul, vec7_mk, vec7_mk, vec7_mk]
  rfl

theorem vec7_one : vec7 α 1 = 0 := by
  rw [← QuotientGroup.mk_one, vec7_mk]
  rfl

theorem card_secKer7 : Nat.card (↥(FFModel.a7Four α).sec ⧸
    (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 2 ^ 4 := by
  have hbij : Function.Bijective (vec7 α) := ⟨vec7_injective α, fun v =>
    ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩, by rw [vec7_mk]; rfl⟩⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

namespace Hat3

variable {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
  (hZ : Nat.card (Subgroup.center Q) = 3) (φ : Q →* Perm (Fin 6))
  (hker : ∀ q, φ q = 1 → q ∈ Subgroup.center Q) (hrange : φ.range = alternatingGroup (Fin 6))
include hZ hker hrange

theorem fix_of_cover_id (β : Q →* Q) (hβ : ∀ q, φ (β q) = φ q) {ζ : Q}
    (hζ : ζ ∈ Subgroup.center Q) : β ζ = ζ := by
  obtain ⟨X, hX⟩ : A6.Hat3.c1 ∈ φ.range := by
    rw [hrange]; exact Perm.mem_alternatingGroup.2 A6.Hat3.c_facts.1
  obtain ⟨Y, hY⟩ : A6.Hat3.c2 ∈ φ.range := by
    rw [hrange]; exact Perm.mem_alternatingGroup.2 A6.Hat3.c_facts.2.1
  set γ := X * Y * X⁻¹ * Y⁻¹ with hγ
  have hγc : γ ∈ Subgroup.center Q := hker _ (by
    rw [hγ, map_mul, map_mul, map_mul, map_inv, map_inv, hX, hY]; exact A6.Hat3.c_facts.2.2.1)
  have hγ1 : γ ≠ 1 := by
    intro h
    apply A6.Hat3.comm_ne hZ φ hker hrange hX hY
    calc X * Y = γ * Y * X := by rw [hγ]; group
      _ = Y * X := by rw [h, one_mul]
  have hκ₁ : X⁻¹ * β X ∈ Subgroup.center Q := hker _ (by
    rw [map_mul, map_inv, hβ, inv_mul_cancel])
  have hκ₂ : Y⁻¹ * β Y ∈ Subgroup.center Q := hker _ (by
    rw [map_mul, map_inv, hβ, inv_mul_cancel])
  have hβγ : β γ = γ := by
    generalize hk₁ : X⁻¹ * β X = κ₁ at hκ₁
    generalize hk₂ : Y⁻¹ * β Y = κ₂ at hκ₂
    have eX : β X = X * κ₁ := by rw [← hk₁]; group
    have eY : β Y = Y * κ₂ := by rw [← hk₂]; group
    have e1 := Subgroup.mem_center_iff.mp hκ₁
    have e2 := Subgroup.mem_center_iff.mp hκ₂
    rw [hγ, map_mul, map_mul, map_mul, map_inv, map_inv, eX, eY]
    calc X * κ₁ * (Y * κ₂) * (X * κ₁)⁻¹ * (Y * κ₂)⁻¹
        = X * (κ₁ * (Y * κ₂)) * κ₁⁻¹ * X⁻¹ * (Y * κ₂)⁻¹ := by group
      _ = X * ((Y * κ₂) * κ₁) * κ₁⁻¹ * X⁻¹ * (Y * κ₂)⁻¹ := by rw [← e1 (Y * κ₂)]
      _ = X * Y * (κ₂ * X⁻¹) * κ₂⁻¹ * Y⁻¹ := by group
      _ = X * Y * (X⁻¹ * κ₂) * κ₂⁻¹ * Y⁻¹ := by rw [← e2 X⁻¹]
      _ = X * Y * X⁻¹ * Y⁻¹ := by group
  have hγ3 : γ ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨γ, hγc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hZγ : Subgroup.center Q = Subgroup.zpowers γ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγc) ?_).symm
    rw [Nat.card_zpowers, hord, hZ]
  rw [hZγ] at hζ
  obtain ⟨k, rfl⟩ := hζ
  simp only
  rw [map_zpow, hβγ]

theorem fix_of_cover (β : Q →* Q) {s : Perm (Fin 6)} (hs : s ∈ alternatingGroup (Fin 6))
    (hβ : ∀ q, φ (β q) = s * φ q * s⁻¹) {ζ : Q} (hζ : ζ ∈ Subgroup.center Q) : β ζ = ζ := by
  obtain ⟨q₀, hq₀⟩ : s ∈ φ.range := by rw [hrange]; exact hs
  let β' : Q →* Q := (MulAut.conj q₀⁻¹).toMonoidHom.comp β
  have hβ' : ∀ q, φ (β' q) = φ q := by
    intro q
    show φ (q₀⁻¹ * β q * q₀⁻¹⁻¹) = φ q
    rw [inv_inv, map_mul, map_mul, map_inv, hβ, hq₀]
    group
  have h := fix_of_cover_id hZ φ hker hrange β' hβ' hζ
  have e : β ζ = q₀ * β' ζ * q₀⁻¹ := by
    show β ζ = q₀ * (q₀⁻¹ * β ζ * q₀⁻¹⁻¹) * q₀⁻¹
    group
  rw [e, h, Subgroup.mem_center_iff.mp hζ q₀, mul_inv_cancel_right]

end Hat3

theorem exists_conj_of_three {E : Type*} [Group E] [Finite E] {N : Subgroup E} [N.Normal]
    (hN : IsPGroup 2 N) (hidx : N.index = 3) {x y : E} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxN : x ∉ N) (hxy : x⁻¹ * y ∈ N) : ∃ d ∈ N, d * x * d⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ N.one_mem)
  have hyN : y ∉ N := fun h => hxN (by
    have := N.mul_mem h (N.inv_mem hxy)
    have e : y * (x⁻¹ * y)⁻¹ = x := by group
    rwa [e] at this)
  have hy1 : y ≠ 1 := fun h => hyN (h ▸ N.one_mem)
  have hox : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy hy1
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hE : Nat.card E = 3 * 2 ^ k := by rw [← N.index_mul_card, hidx, hk]
  have hsyl : ∀ z : E, orderOf z = 3 → IsPGroup 3 (Subgroup.zpowers z) ∧
      ¬ 3 ∣ (Subgroup.zpowers z).index := by
    intro z hz
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), ?_⟩
    have h1 := (Subgroup.zpowers z).index_mul_card
    rw [hE, Nat.card_zpowers, hz] at h1
    have hi : (Subgroup.zpowers z).index = 2 ^ k := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
      rw [h1, mul_comm]
    rw [hi]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  let P : Sylow 3 E := (hsyl x hox).1.toSylow (hsyl x hox).2
  let P' : Sylow 3 E := (hsyl y hoy).1.toSylow (hsyl y hoy).2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P P'
  have hgen : ∃ j : ℕ, g * x ^ j ∈ N := by
    have hq : Nat.card (E ⧸ N) = 3 := hidx
    have hxq : (QuotientGroup.mk x : E ⧸ N) ≠ 1 := by
      rwa [Ne, QuotientGroup.eq_one_iff]
    have hoq : orderOf (QuotientGroup.mk x : E ⧸ N) = 3 :=
      orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]) hxq
    have htop : Subgroup.zpowers (QuotientGroup.mk x : E ⧸ N) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hoq, hq])
    have hmem : (QuotientGroup.mk g⁻¹ : E ⧸ N) ∈ Subgroup.zpowers (QuotientGroup.mk x : E ⧸ N) :=
      htop ▸ Subgroup.mem_top _
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 hmem
    refine ⟨j, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow, hj,
      QuotientGroup.mk_inv, mul_inv_cancel]
  obtain ⟨j, hj⟩ := hgen
  set d := g * x ^ j with hd
  have hdP : d • P = P' := by
    rw [hd, mul_smul]
    have : x ^ j • P = P := by
      rw [Sylow.smul_eq_iff_mem_normalizer]
      exact Subgroup.le_normalizer (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j)
    rw [this, hg]
  have hdx : d * x * d⁻¹ ∈ Subgroup.zpowers y := by
    have h1 : d * x * d⁻¹ ∈ ((d • P : Sylow 3 E) : Subgroup E) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      show (MulAut.conj d)⁻¹ • (d * x * d⁻¹) ∈ Subgroup.zpowers x
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
      have e : d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x := by group
      rw [e]
      exact Subgroup.mem_zpowers x
    rw [hdP] at h1
    exact h1
  rw [← mem_powers_iff_mem_zpowers] at hdx
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 hdx
  have hdxN : x⁻¹ * (d * x * d⁻¹) ∈ N := by
    have h1 : x⁻¹ * d * x ∈ N := by
      have := (inferInstance : N.Normal).conj_mem d hj x⁻¹
      rwa [inv_inv] at this
    have e : x⁻¹ * (d * x * d⁻¹) = (x⁻¹ * d * x) * d⁻¹ := by group
    rw [e]
    exact N.mul_mem h1 (N.inv_mem hj)
  have hi3 : i % 3 = 1 := by
    have hyi : y ^ i = y ^ (i % 3) := by
      conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hy, one_pow, mul_one]
    rw [hyi] at hi
    have h3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : i % 3
    · exfalso
      rw [pow_zero] at hi
      apply hx1
      have e : x = d⁻¹ * (d * x * d⁻¹) * d := by group
      rw [e, ← hi]
      group
    · rfl
    · exfalso
      rw [← hi] at hdxN
      apply hyN
      have h1 := N.mul_mem (N.inv_mem hxy) hdxN
      have e : (x⁻¹ * y)⁻¹ * (x⁻¹ * y ^ 2) = y := by
        rw [pow_two]
        group
      rwa [e] at h1
  refine ⟨d, hj, ?_⟩
  rw [← hi, ← Nat.mod_add_div i 3, hi3, pow_add, pow_mul, hy, one_pow, mul_one, pow_one]

end A6L76T

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]
  {α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)}

@[expose] noncomputable def cls7 (C : S.Ctx76 H K (FFModel.a7Four α))
    (u : ↥(conjClosure S.V3 H)) : Fin 4 → ZMod 2 :=
  A6L76T.vec7 α (C.βU u)

variable (C : S.Ctx76 H K (FFModel.a7Four α))

theorem cls7_mul (u u' : ↥(conjClosure S.V3 H)) : C.cls7 (u * u') = C.cls7 u + C.cls7 u' := by
  rw [cls7, cls7, cls7, map_mul, A6L76T.vec7_mul]

theorem cls7_eq_zero_iff (u : ↥(conjClosure S.V3 H)) : C.cls7 u = 0 ↔ C.βU u = 1 := by
  rw [cls7, ← A6L76T.vec7_one α]
  exact (A6L76T.vec7_injective α).eq_iff

theorem cls7_inj {u u' : ↥(conjClosure S.V3 H)} (h : C.cls7 u = C.cls7 u') :
    C.βU u = C.βU u' :=
  A6L76T.vec7_injective α h

theorem cls7_equiv (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) :
    C.cls7 ⟨_, hku⟩ = A6L76T.mat7 α (C.α k) *ᵥ C.cls7 u := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU u)
  rw [cls7, C.βU_equiv k u hku m.2 hxm.symm, A6L76T.vec7_mk, cls7, ← hxm, A6L76T.vec7_mk]
  rfl

theorem βU_eq_one_iff_V1₇ (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) (u : ↥(conjClosure S.V3 H)) :
    C.βU u = 1 ↔ (u : G) ∈ fsuV1 T V := by
  obtain ⟨-, -, -, -, -, -, -, -, hβk, -⟩ := C.hR
  rw [βU, MonoidHom.comp_apply, hβk, hfix, bot_inf_eq, Subgroup.mem_bot, C.ι_coe,
    A6Mod.secMk_eq_one_iff]

@[expose] noncomputable def cv27 : Fin 4 → ZMod 2 := C.cls7 ⟨S.v2, S.v2_mem_UH H⟩

@[expose] noncomputable def cv2g7 {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) : Fin 4 → ZMod 2 :=
  C.cls7 ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩

variable {g : ↥(Subgroup.normalizer (V : Set G))} (hgL : (g : G) ∈ S.L1)
  (hg : S.frame.ρ g = swap 0 1 * swap 1 2)

include hg in
theorem cls7_V3 {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H) :
    C.cls7 ⟨u, huU⟩ = 0 ∨ A6L76Q.In3v C.cv27 (C.cv2g7 hgL) (C.cls7 ⟨u, huU⟩) := by
  rcases C.classes_V3_gen hgL hg hu3 huU with h | h | h | h
  · exact Or.inl ((C.cls7_eq_zero_iff _).2 h)
  · exact Or.inr (Or.inl (congrArg (A6L76T.vec7 α) h))
  · exact Or.inr (Or.inr (Or.inl (congrArg (A6L76T.vec7 α) h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [cls7, h, A6L76T.vec7_mul]
    rfl

include hg in
theorem reps7_V3 {z : Fin 4 → ZMod 2} (hz : z = 0 ∨ A6L76Q.In3v C.cv27 (C.cv2g7 hgL) z) :
    ∃ v ∈ S.V3, ∃ hvU : v ∈ conjClosure S.V3 H, C.cls7 ⟨v, hvU⟩ = z := by
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨1, S.V3.one_mem, (conjClosure S.V3 H).one_mem, ?_⟩
    rw [C.cls7_eq_zero_iff, show (⟨1, (conjClosure S.V3 H).one_mem⟩ : ↥(conjClosure S.V3 H)) =
      1 from rfl, map_one]
  · exact ⟨S.v2, S.v2_mem_V3, S.v2_mem_UH H, rfl⟩
  · exact ⟨_, S.conj_v2_mem_V3 hg, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H), rfl⟩
  · refine ⟨_, S.V3.mul_mem S.v2_mem_V3 (S.conj_v2_mem_V3 hg),
      (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H) (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)),
      ?_⟩
    rw [show (⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H)
      (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ : ↥(conjClosure S.V3 H)) =
      ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ from rfl,
      cls7_mul]
    rfl

include hg in
theorem conj_mem_V3_of_pres7 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) {d : G} (hdK : d ∈ K)
    (hd : ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv27 (C.cv2g7 hgL) z) →
      (A6L76T.mat7 α (C.α ⟨d, hdK⟩) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv27 (C.cv2g7 hgL) (A6L76T.mat7 α (C.α ⟨d, hdK⟩) *ᵥ z)))
    {v : G} (hv : v ∈ S.V3) : d * v * d⁻¹ ∈ S.V3 := by
  have hvU : v ∈ conjClosure S.V3 H := le_conjClosure _ _ hv
  have hc := C.cls7_equiv ⟨d, hdK⟩ ⟨v, hvU⟩ (C.conj_mem_UH hdK hvU)
  obtain ⟨v', hv'3, hv'U, hv'⟩ := C.reps7_V3 hgL hg (z := C.cls7 ⟨_, C.conj_mem_UH hdK hvU⟩)
    (by rw [hc]; exact hd _ (C.cls7_V3 hgL hg hv hvU))
  have h1 := C.cls7_inj hv'
  have hmem : d * v * d⁻¹ * v'⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem (C.conj_mem_UH hdK hvU) ((conjClosure S.V3 H).inv_mem hv'U)
  have h2 : C.βU ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥(conjClosure S.V3 H)) =
        ⟨_, C.conj_mem_UH hdK hvU⟩ * (⟨v', hv'U⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, ← h1, mul_inv_cancel]
  have h3 := (C.βU_eq_one_iff_V1₇ hfix _).1 h2
  have e : d * v * d⁻¹ = (d * v * d⁻¹ * v'⁻¹) * v' := by group
  rw [e]
  exact S.V3.mul_mem (S.fsuV1_le_V3 h3) hv'3

theorem hat_of_a7 (h1337 : Stmt13_3_7)
    (C : S.Ctx76 H K (FFModel.a7Four α))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) : IsHatA6 L := by
  by_contra hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (FFModel.a7Four α).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  have hle := S.pRank_three_NV3_le_one C.h13315 h1337 hhat C.hH
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hx0 : C.cv27 ≠ 0 := fun h => C.βU_v2_ne_one ((C.cls7_eq_zero_iff _).1 h)
  have hy0 : C.cv2g7 hgL ≠ 0 := fun h => C.βU_v2g_ne_one hgL ((C.cls7_eq_zero_iff _).1 h)
  have hxy : C.cv27 ≠ C.cv2g7 hgL := fun h => C.βU_v2_ne_v2g hgL hg (C.cls7_inj h)
  obtain ⟨x, y, hE, hxs, hys⟩ := A6L76S.exists_e9_lineStab α hx0 hy0 hxy
  set Y : Subgroup (FFModel.a7Four α).Gam :=
    (A6L76S.lineStab C.cv27 (C.cv2g7 hgL)).comap (α.toMonoidHom.comp altLift7) with hY
  have hpres : ∀ d : ↥K, C.α d ∈ Y → ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv27 (C.cv2g7 hgL) z) →
      (A6L76T.mat7 α (C.α d) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv27 (C.cv2g7 hgL) (A6L76T.mat7 α (C.α d) *ᵥ z)) := by
    intro d hd z hz
    rcases hz with rfl | hz
    · left
      exact Matrix.mulVec_zero _
    · right
      exact hd z hz
  have h2 : 2 ≤ CFSG.Open.pRank 3 Y :=
    A6L76B.two_le_pRank_of_e9 (show x ∈ Y from hxs) (show y ∈ Y from hys) hE
  have h3 := A6L76B.pRank_map_le C.α C.not_three_dvd_ker (Y.comap C.α)
  rw [Subgroup.map_comap_eq_self_of_surjective C.α_surj] at h3
  have h4 := A6L76F.pRank_le_map_of_not_dvd (p := 3) K.subtype
    (by rw [Subgroup.ker_subtype, Subgroup.card_bot]; norm_num) (Y.comap C.α)
  have hfwd : ∀ d : ↥K, d ∈ Y.comap C.α → ∀ v ∈ S.V3, (d : G) * v * (d : G)⁻¹ ∈ S.V3 :=
    fun d hd v hv => C.conj_mem_V3_of_pres7 hgL hg hfix d.2 (hpres d hd) hv
  have hXN : (Y.comap C.α).map K.subtype ≤ H ⊓ Subgroup.normalizer (S.V3 : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨C.hKH d.2, Subgroup.mem_normalizer_iff.2 fun v => ⟨hfwd d hd v, fun h' => ?_⟩⟩
    have h1 : ((d⁻¹ : ↥K) : G) * ((d : G) * v * (d : G)⁻¹) * ((d⁻¹ : ↥K) : G)⁻¹ ∈ S.V3 :=
      hfwd d⁻¹ ((Y.comap C.α).inv_mem hd) _ h'
    have e : ((d⁻¹ : ↥K) : G) * ((d : G) * v * (d : G)⁻¹) * ((d⁻¹ : ↥K) : G)⁻¹ = v := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h1
  have h5 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hXN
  omega

include C in
theorem card_tildeU_a7 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) :
    Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 2 ^ 4 := by
  obtain ⟨-, -, -, -, -, -, -, hβs, hβk, -⟩ := C.hR
  have hβi : Function.Injective C.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβk u).1 hu
    rw [hfix, bot_inf_eq, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have e1 : Nat.card ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) = Nat.card (Sec
        (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
    rw [C.top, Subgroup.card_top]
  rw [← e1, Nat.card_congr (Equiv.ofBijective _ ⟨hβi, hβs⟩), A6L76T.card_secKer7]

include C in
theorem tilde_eq_a7 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) :
    autSec (autOn H (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 C.hH
  have hK : Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 2520 := by
    rw [← Nat.card_congr C.eπ.toEquiv]
    show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hN := CFSG.QuasithinUnique.L246.C123.normalizer_eq_of_card_2520 C.sq_tildeU
    (by rw [C.card_tildeU_a7 hfix]; rfl) hK
  refine le_antisymm ?_ (autSec_mono (InternalSec.autOn_le_autOn_of_le C.hKH) _ _)
  rw [← hN]
  intro x hx
  obtain ⟨h, -, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV le_rfl).1 hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV C.hKH).2 ⟨h * k * h⁻¹, ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (C.hHK h.2) k).mp hkK
  · intro hy
    obtain ⟨k, hkK, hk⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV C.hKH).2 ⟨h⁻¹ * k * h, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (C.hHK (H.inv_mem h.2)) k).mp hkK
      simpa using this
    · rw [map_mul, map_mul, map_inv, hk]
      group

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
