module

public import CFSG.Quasithin.H13.L32AC32i

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C

theorem sl2_same : ∀ r s b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), r ^ 3 = 1 → r ≠ 1 →
    s ≠ 1 → s ^ 2 = 1 → b * r = r * b → (s * b * s⁻¹ * (b⁻¹ * r)) ^ 2 = 1 → b = r ^ 2 := by
  decide

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} {t₀ : G}

theorem psi_eq_of_mk_eq {V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting147 G T L V H)
    (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V)) {a b : ↥H}
    (haX : (a : G) ∈ L32NSet14.nX T V) (hbX : (b : G) ∈ L32NSet14.nX T V)
    (hab : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a = QuotientGroup.mk' (CFSG.pCore 2 ↥H) b) :
    ψ ⟨a, haX⟩ = ψ ⟨b, hbX⟩ := by
  have hq : (a : G)⁻¹ * b ∈ pCoreOf 2 H := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hab
    simpa using hab
  have htriv := pCoreOf_le_trivSub S S14 hq
  have h1 : ψ (⟨a, haX⟩⁻¹ * ⟨b, hbX⟩) = 1 := (hψ _).mpr htriv
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem psi_pow_of_mk_pow {V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting147 G T L V H)
    (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V)) {a : ↥H}
    (haX : (a : G) ∈ L32NSet14.nX T V) {m : ℕ}
    (ha : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a) ^ m = 1) : ψ ⟨a, haX⟩ ^ m = 1 := by
  have hX : ((a ^ m : ↥H) : G) ∈ L32NSet14.nX T V := by simpa using pow_mem haX m
  have h1X : ((1 : ↥H) : G) ∈ L32NSet14.nX T V := one_mem _
  have h1 := psi_eq_of_mk_eq S S14 hψ (a := a ^ m) (b := 1) hX h1X
    (by rw [map_pow, ha, map_one])
  have e1 : (⟨a, haX⟩ : ↥(L32NSet14.nX T V)) ^ m = ⟨((a ^ m : ↥H) : G), hX⟩ :=
    Subtype.ext (by simp)
  have e2 : (⟨((1 : ↥H) : G), h1X⟩ : ↥(L32NSet14.nX T V)) = 1 := Subtype.ext rfl
  rw [← map_pow, e1, h1, e2, map_one]

namespace CtxL2Same

variable (C : CtxL2 T L V H K t₀ 2)
include C

theorem exists_same_action (hA37 : A37ForSQTK) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting G T L V V₂) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1)
    (hfpf : ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    {k₁ k₂ : ↥H ⧸ CFSG.pCore 2 ↥H} (hk₁K : k₁ ∈ modO2Image H K)
    (hk₂K : k₂ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)))
    (he : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ = k₁ * k₂)
    (hk₁ : ∀ m ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      m * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k₁ * m * k₁⁻¹)
    (hk₂ : ∀ m ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * m *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k₂ * m * k₂⁻¹) :
    ∃ β₁ β₂ : ↥H, QuotientGroup.mk' (CFSG.pCore 2 ↥H) β₁ = k₁ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) β₂ = k₂ ∧
      (β₁ : G) ∈ L32NSet14.nX T V ∧ (β₂ : G) ∈ L32NSet14.nX T V ∧
      (β₁ : G)⁻¹ * β₂ ∈ L32NSet14.trivSub V (fsuV1 T V) ∧
      (y ^ 2)⁻¹ * β₁ ∈ L32NSet14.trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hyH : y ∈ H := Setting147.l1H' C.S hy
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  have hS1 := C.mk_l1_mem_normalizer_szS1 hA37 h1222 h1332 h1334
  have hk₁B := C.k₁_mem_szB1 h1222 h1332 h1334 hy hy3 hk₁K hk₁
  have hk₂B := C.k₂_mem_szB2 h1222 h1332 h1334 hy hy3 hk₂K hk₂
  obtain ⟨β₁, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) k₁
  obtain ⟨β₂, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) k₂
  have hB12 : ∀ β : ↥H, mk β ∈ szB1 T H K ∨ mk β ∈ (szB1 T H K).map
      (MulAut.conj (mk ⟨t₀, C.ht₀H⟩) : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) →
      (β : G) ∈ L32NSet14.nX T V := by
    intro β hβ
    have hβ' : mk β ∈ szB12 T H K (mk ⟨t₀, C.ht₀H⟩) ⊔ modO2Image H (l1 T L V ⊔ T) := by
      refine Subgroup.mem_sup_left ?_
      rcases hβ with h | h
      · exact Subgroup.mem_sup_left h
      · exact Subgroup.mem_sup_right h
    have hβL := C.toCtxS.mem_normalizer_L hA37 h29 h1222 h1332 h1334 hS1 hβ'
    exact C.toCtxS.mem_nX h1332 h1334 β.2 hβL
  have hβ₁X := hB12 β₁ (Or.inl hk₁B)
  have hβ₂X := hB12 β₂ (Or.inr hk₂B)
  refine ⟨β₁, β₂, rfl, rfl, hβ₁X, hβ₂X, ?_⟩
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  have hyX : y ∈ L32NSet14.nX T V := S14.L1_le_X (by rw [hl1]; exact hy)
  obtain ⟨t, htT, htL, htn⟩ := exists_TL_not_triv C.S.hyp h1332 S14
  have htH : t ∈ H := C.hTH htT
  have htX : t ∈ L32NSet14.nX T V := S14.T_le_X htT
  have htN : t ∉ Subgroup.normalizer (K : Set G) := fun h =>
    C.false_of_not_swap hA37 h29 h1222 h1332 h1334 S14 hy hy3 hfpf htT htL htn h
  set r := ψ ⟨y, hyX⟩ with hr
  set s := ψ ⟨t, htX⟩ with hs
  set b₁ := ψ ⟨β₁, hβ₁X⟩ with hb₁
  set b₂ := ψ ⟨β₂, hβ₂X⟩ with hb₂
  have hr3 : r ^ 3 = 1 := by
    rw [hr, ← map_pow]
    convert map_one ψ using 2
    exact Subtype.ext (by simpa using hy3)
  have hr1 : r ≠ 1 := by
    intro h
    have hyt := (hψ _).mp h
    have hle : V ≤ fsuV1 T V := fun v hv =>
      hfpf v hv ((L32NSet14.mem_trivSub.mp hyt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  have hs1 : s ≠ 1 := fun h => htn ((hψ _).mp h)
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := C.S.hyp.fsu.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [hs, ← map_pow]
    convert map_one ψ using 2
    exact Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hc12 : mk β₁ * mk β₂ = mk β₂ * mk β₁ := C.commute_kb hA37 hk₁K hk₂K
  have hprod : b₁ * b₂ = r := by
    rw [hb₁, hb₂, hr, ← map_mul]
    exact psi_eq_of_mk_eq C.S S14 hψ (a := β₁ * β₂) (b := ⟨y, hyH⟩) (mul_mem hβ₁X hβ₂X) hyX
      (by rw [map_mul, ← he])
  have hcomm1 : b₁ * r = r * b₁ := by
    rw [hb₁, hr, ← map_mul, ← map_mul]
    refine psi_eq_of_mk_eq C.S S14 hψ (a := β₁ * ⟨y, hyH⟩) (b := ⟨y, hyH⟩ * β₁)
      (mul_mem hβ₁X hyX) (mul_mem hyX hβ₁X) ?_
    rw [map_mul, map_mul, he]
    calc mk β₁ * (mk β₁ * mk β₂) = mk β₁ * (mk β₂ * mk β₁) := by rw [hc12]
      _ = mk β₁ * mk β₂ * mk β₁ := by group
  have hcomm2 : b₂ * r = r * b₂ := by
    rw [hb₂, hr, ← map_mul, ← map_mul]
    refine psi_eq_of_mk_eq C.S S14 hψ (a := β₂ * ⟨y, hyH⟩) (b := ⟨y, hyH⟩ * β₂)
      (mul_mem hβ₂X hyX) (mul_mem hyX hβ₂X) ?_
    rw [map_mul, map_mul, he]
    calc mk β₂ * (mk β₁ * mk β₂) = (mk β₂ * mk β₁) * mk β₂ := by group
      _ = (mk β₁ * mk β₂) * mk β₂ := by rw [hc12]
  have ht₀t : t₀⁻¹ * t ∈ Subgroup.normalizer (K : Set G) :=
    (C.two t htH).resolve_left htN
  have htt₀ : t * t₀ ∈ Subgroup.normalizer (K : Set G) := by
    rcases C.two (t * t₀) (mul_mem htH C.ht₀H) with h | h
    · exact h
    · exfalso
      apply C.ht₀N
      have := mul_mem (inv_mem ht₀t) h
      rwa [show (t₀⁻¹ * t)⁻¹ * (t₀⁻¹ * (t * t₀)) = t₀ by group] at this
  set tb := mk ⟨t, htH⟩ with htb
  have hK₁K₂ : tb * mk β₁ * tb⁻¹ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := by
    obtain ⟨κ, hκ, hκe⟩ := mem_modO2Image'.mp hk₁K
    refine mem_modO2Image'.mpr ⟨⟨t, htH⟩ * κ * ⟨t, htH⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv,
      hκe]⟩
    refine ⟨(t₀⁻¹ * t) * κ * (t₀⁻¹ * t)⁻¹,
      (Subgroup.mem_normalizer_iff.mp ht₀t _).mp hκ, ?_⟩
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hK₂K₁ : tb * mk β₂ * tb⁻¹ ∈ modO2Image H K := by
    obtain ⟨κ, hκ, hκe⟩ := mem_modO2Image'.mp hk₂K
    obtain ⟨κ', hκ', hκ'e⟩ := Subgroup.mem_map.mp hκ
    refine mem_modO2Image'.mpr ⟨⟨t, htH⟩ * κ * ⟨t, htH⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv,
      hκe]⟩
    have e : ((⟨t, htH⟩ * κ * ⟨t, htH⟩⁻¹ : ↥H) : G) = (t * t₀) * κ' * (t * t₀)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hκ'e]
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp htt₀ _).mp hκ'
  obtain ⟨m, hm⟩ := comm_x_pow_two S14 (by rw [hl1]; exact hy) hy3 hfpf htT htn
  set c₁ := tb * mk β₂ * tb⁻¹ * mk β₁ with hc₁
  set c₂ := tb * mk β₁ * tb⁻¹ * mk β₂ with hc₂
  have hc₁K : c₁ ∈ modO2Image H K := mul_mem hK₂K₁ hk₁K
  have hc₂K : c₂ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := mul_mem hK₁K₂ hk₂K
  have ho : mk ⟨t * y * t⁻¹ * y, by
      exact mul_mem (mul_mem (mul_mem htH hyH) (inv_mem htH)) hyH⟩ = c₂ * c₁ := by
    have e1 : mk ⟨t * y * t⁻¹ * y, mul_mem (mul_mem (mul_mem htH hyH) (inv_mem htH)) hyH⟩ =
        tb * (mk β₁ * mk β₂) * tb⁻¹ * (mk β₁ * mk β₂) := by
      rw [← he, htb, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e1, hc₁, hc₂]
    have hcA : ∀ a ∈ modO2Image H K, ∀ b ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
        a * b = b * a := fun a ha b hb => C.commute_kb hA37 ha hb
    have x1 := hcA _ hK₂K₁ _ hK₁K₂
    have x2 := hcA _ hk₁K _ hK₁K₂
    have x3 := hcA _ hK₂K₁ _ hk₂K
    calc tb * (mk β₁ * mk β₂) * tb⁻¹ * (mk β₁ * mk β₂)
        = (tb * mk β₁ * tb⁻¹) * (tb * mk β₂ * tb⁻¹) * mk β₁ * mk β₂ := by group
      _ = (tb * mk β₂ * tb⁻¹) * (tb * mk β₁ * tb⁻¹) * mk β₁ * mk β₂ := by rw [x1]
      _ = (tb * mk β₂ * tb⁻¹) * ((tb * mk β₁ * tb⁻¹) * mk β₁) * mk β₂ := by group
      _ = (tb * mk β₂ * tb⁻¹) * (mk β₁ * (tb * mk β₁ * tb⁻¹)) * mk β₂ := by rw [x2]
      _ = ((tb * mk β₂ * tb⁻¹) * mk β₁) * ((tb * mk β₁ * tb⁻¹) * mk β₂) := by group
      _ = ((tb * mk β₁ * tb⁻¹) * mk β₂) * ((tb * mk β₂ * tb⁻¹) * mk β₁) := by
        rw [(hcA _ hc₁K _ hc₂K)]
  have hc₂2 : c₂ ^ 2 ^ m = 1 := by
    have h1 : (c₂ * c₁) ^ 2 ^ m = 1 := by
      rw [← ho, ← map_pow]
      convert map_one mk using 2
      exact Subtype.ext (by simpa using hm)
    exact pow_eq_one_of_mul (N₁ := modO2Image H (K.map (MulAut.conj t₀ : G →* G)))
      (N₂ := modO2Image H K) (fun a ha b hb => (C.commute_kb hA37 hb ha).symm)
      (fun z hz hz' => C.eq_one_of_mem_kb_kt hA37 hz' hz) hc₂K hc₁K h1
  have hwH : t * β₁ * t⁻¹ * β₂ ∈ H :=
    mul_mem (mul_mem (mul_mem htH β₁.2) (inv_mem htH)) β₂.2
  have hwX : t * β₁ * t⁻¹ * β₂ ∈ L32NSet14.nX T V :=
    mul_mem (mul_mem (mul_mem htX hβ₁X) (inv_mem htX)) hβ₂X
  have hw : (s * b₁ * s⁻¹ * b₂) ^ 2 = 1 := by
    have h1 := psi_pow_of_mk_pow C.S S14 hψ (a := ⟨t * β₁ * t⁻¹ * β₂, hwH⟩) hwX
      (m := 2 ^ m) (by
        have : mk ⟨t * β₁ * t⁻¹ * β₂, hwH⟩ = c₂ := by
          rw [hc₂, htb, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          rfl
        rw [this]
        exact hc₂2)
    have h2 : ψ ⟨t * β₁ * t⁻¹ * β₂, hwX⟩ = s * b₁ * s⁻¹ * b₂ := by
      rw [hs, hb₁, hb₂, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [h2] at h1
    exact L32NSet14.sl2_sq_of_two h1
  have hb₂e : b₂ = b₁⁻¹ * r := by rw [← hprod]; group
  have h₁ := sl2_same r s b₁ hr3 hr1 hs1 hs2 hcomm1 (by rw [← hb₂e]; exact hw)
  have h₂ : b₂ = r ^ 2 := by
    rw [hb₂e, h₁]
    have hr2 : r⁻¹ = r ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact hr3
    calc (r ^ 2)⁻¹ * r = r⁻¹ := by group
      _ = r ^ 2 := hr2
  constructor
  · have : ψ (⟨β₁, hβ₁X⟩⁻¹ * ⟨β₂, hβ₂X⟩) = 1 := by
      rw [map_mul, map_inv, ← hb₁, ← hb₂, h₁, h₂, inv_mul_cancel]
    exact (hψ _).mp this
  · have hy2X : y ^ 2 ∈ L32NSet14.nX T V := pow_mem hyX 2
    have : ψ (⟨y ^ 2, hy2X⟩⁻¹ * ⟨β₁, hβ₁X⟩) = 1 := by
      have e : (⟨y ^ 2, hy2X⟩ : ↥(L32NSet14.nX T V)) = ⟨y, hyX⟩ ^ 2 := Subtype.ext (by simp)
      rw [map_mul, map_inv, e, map_pow, ← hr, ← hb₁, h₁, inv_mul_cancel]
    exact (hψ _).mp this

end CtxL2Same

end CFSG.Quasithin.H13.L32A.L2
