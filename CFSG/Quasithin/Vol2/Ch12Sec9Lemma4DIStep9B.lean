module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep9
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep8
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep9A

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def stabVec {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (v : M) :
    Subgroup (M ≃ₗ[ZMod 2] M) where
  carrier := {γ | γ v = v}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    show a (b v) = v
    rw [hb, ha]
  inv_mem' := fun {a} ha => by
    show a.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact ha.symm

@[expose] def k0Sub {V V₁ : Subgroup G} (K₁ : Subgroup G) (D : HatModelU (u128 V V₁))
    (v : D.V) : Subgroup G :=
  K₁ ⊓ preimgSub D (stabVec v)

theorem mem_k0Sub {V V₁ : Subgroup G} {K₁ : Subgroup G} {D : HatModelU (u128 V V₁)} {v : D.V}
    {k : G} : k ∈ k0Sub K₁ D v ↔
      k ∈ K₁ ∧ ∃ hk : k ∈ Subgroup.normalizer (u128 V V₁ : Set G), D.ρ ⟨k, hk⟩ v = v :=
  Iff.rfl

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem ccF_mem_zU (E : DIEnv T L V V₁ V₂ K₁ g D) {k : G}
    (hk : k ∈ k0Sub K₁ D (D.π E.a)) : ccF E.a k ∈ zU128 V V₁ := by
  obtain ⟨hkK, hkN, hρ⟩ := mem_k0Sub.1 hk
  have haU : E.a ∈ u128 V V₁ := le_conjClosure V _ (E.hs.v2.1 E.haV₂)
  have hkaU : k * E.a * k⁻¹ ∈ u128 V V₁ := (Subgroup.mem_normalizer_iff.1 hkN E.a).1 haU
  have hU : ccF E.a k ∈ u128 V V₁ :=
    Subgroup.mul_mem _ hkaU (Subgroup.inv_mem _ haU)
  have hπk : D.π (k * E.a * k⁻¹) = D.π E.a := by
    rw [← D.ρ_π ⟨k, hkN⟩ E.a haU]
    exact hρ
  have h0 : D.π (ccF E.a k) = 0 := by
    unfold ccF
    rw [D.π_mul _ hkaU _ (Subgroup.inv_mem _ haU), hπk, L128A.HatU.π_inv D haU, add_neg_cancel]
  exact (L128A.HatU.π_eq_zero_iff D hU).1 h0

theorem ccF_sq (E : DIEnv T L V V₁ V₂ K₁ g D) {k : G}
    (hk : k ∈ k0Sub K₁ D (D.π E.a)) : ccF E.a k ^ 2 = 1 := by
  obtain ⟨hkK, hkN, hρ⟩ := mem_k0Sub.1 hk
  have hcZ := ccF_mem_zU E hk
  have haU : E.a ∈ u128 V V₁ := le_conjClosure V _ (E.hs.v2.1 E.haV₂)
  have ha2 : E.a ^ 2 = 1 := sq_eq_one_of_cx E.hcx E.a (E.hs.v2.1 E.haV₂)
  have hcomm : E.a * ccF E.a k = ccF E.a k * E.a :=
    (mem_centerOf_iff'.1 hcZ).2 E.a haU
  have hka : k * E.a * k⁻¹ = ccF E.a k * E.a := by
    unfold ccF; group
  have hsq : (k * E.a * k⁻¹) ^ 2 = 1 := by
    have e : (k * E.a * k⁻¹) ^ 2 = k * E.a ^ 2 * k⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [e, ha2, mul_one, mul_inv_cancel]
  rw [hka, pow_two] at hsq
  have e2 : ccF E.a k * E.a * (ccF E.a k * E.a) = ccF E.a k ^ 2 * E.a ^ 2 := by
    rw [pow_two, pow_two]
    calc ccF E.a k * E.a * (ccF E.a k * E.a) = ccF E.a k * (E.a * ccF E.a k) * E.a := by group
      _ = ccF E.a k * (ccF E.a k * E.a) * E.a := by rw [hcomm]
      _ = ccF E.a k * ccF E.a k * (E.a * E.a) := by group
  rw [e2, ha2, mul_one] at hsq
  exact hsq

theorem V2_coset (E : DIEnv T L V V₁ V₂ K₁ g D) {w : G} (hw : w ∈ V₂) (hw1 : w ∉ V₁) :
    w * E.a⁻¹ ∈ V₁ := by
  have hV₁2 : Nat.card V₁ = 2 := card_V₁ E.hs
  have hV₂4 : Nat.card V₂ = 4 := card_V₂ E.hs
  obtain ⟨z, hz, hz1, -⟩ := L128P.exists_gens hV₁2 hV₂4
  rcases L128P.eq_of_mem_four E.hs.le hV₁2 hV₂4 hz hz1 E.haV₁ E.haV₂ hw with h | h | h | h
  · exact absurd (h ▸ V₁.one_mem) hw1
  · exact absurd (h ▸ hz) hw1
  · rw [h, mul_inv_cancel]; exact V₁.one_mem
  · rw [h, mul_inv_cancel_right]; exact hz

theorem ccF_T_mem_V1 (E : DIEnv T L V V₁ V₂ K₁ g D) {t : G} (ht : t ∈ T) (htK : t ∈ K₁) :
    ccF E.a t ∈ V₁ := by
  have hTN1 : t ∈ Subgroup.normalizer (V₁ : Set G) := E.hK₁H htK
  have hw : t * E.a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 (E.hs.v2.2.2 ht) E.a).1 E.haV₂
  have hw1 : t * E.a * t⁻¹ ∉ V₁ := by
    intro h
    apply E.haV₁
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hTN1) _).1 h
    simpa [mul_assoc] using h2
  have := V2_coset E hw hw1
  unfold ccF
  exact this

theorem T_inf_K1_le_K0 (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) {t : G} (ht : t ∈ T) (htK : t ∈ K₁) :
    t ∈ k0Sub K₁ D (D.π E.a) := by
  have haU : E.a ∈ u128 V V₁ := le_conjClosure V _ (E.hs.v2.1 E.haV₂)
  have htN : t ∈ Subgroup.normalizer (u128 V V₁ : Set G) := E.hK₁U htK
  refine mem_k0Sub.2 ⟨htK, htN, ?_⟩
  have hcZ : ccF E.a t ∈ zU128 V V₁ := V₁_le_zU h1222 h12213 E.hs (ccF_T_mem_V1 E ht htK)
  have hcU : ccF E.a t ∈ u128 V V₁ := zU_le_u128 hcZ
  have hπ0 : D.π (ccF E.a t) = 0 := (L128A.HatU.π_eq_zero_iff D hcU).2 hcZ
  have e : t * E.a * t⁻¹ = ccF E.a t * E.a := by unfold ccF; group
  rw [D.ρ_π ⟨t, htN⟩ E.a haU, e, D.π_mul _ hcU _ haU, hπ0, zero_add]

theorem T_inf_K0_odd (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hK₁N : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁) :
    ¬ 2 ∣ (T ⊓ k0Sub K₁ D (D.π E.a)).relIndex (k0Sub K₁ D (D.π E.a)) := by
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := E.hs.v1.2.2
  have hTodd : ¬ 2 ∣ T.relIndex (Subgroup.normalizer (V₁ : Set G)) := by
    intro h2
    apply E.hcx.hyp.hyp.sylow.2
    exact dvd_trans h2 (Dvd.intro _ (Subgroup.relIndex_mul_index hTN))
  have hsup : ∀ g' ∈ K₁ ⊔ T, ∀ k ∈ K₁, g' * k * g'⁻¹ ∈ K₁ := fun g' hg' k hk =>
    hK₁N g' (sup_le E.hK₁H hTN hg') k hk
  have hrel := relIndex_sup_eq_of_normalizes hsup
  have hm1 := Subgroup.relIndex_mul_relIndex T (K₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G))
    le_sup_right (sup_le E.hK₁H hTN)
  have hK1odd : ¬ 2 ∣ T.relIndex K₁ := by
    intro h2
    apply hTodd
    rw [← hm1, hrel]
    exact Dvd.dvd.mul_right h2 _
  have hK0K1 : k0Sub K₁ D (D.π E.a) ≤ K₁ := inf_le_left
  have hTK : T ⊓ k0Sub K₁ D (D.π E.a) = T ⊓ K₁ :=
    le_antisymm (inf_le_inf_left T hK0K1) (fun t ht => Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 ht).1, T_inf_K1_le_K0 E h1222 h12213 (Subgroup.mem_inf.1 ht).1
        (Subgroup.mem_inf.1 ht).2⟩)
  have hm := Subgroup.relIndex_mul_relIndex (T ⊓ k0Sub K₁ D (D.π E.a)) (k0Sub K₁ D (D.π E.a))
    K₁ inf_le_right hK0K1
  have hT1 : (T ⊓ k0Sub K₁ D (D.π E.a)).relIndex K₁ = T.relIndex K₁ := by
    rw [hTK]
    exact Subgroup.inf_relIndex_right T K₁
  intro h2
  apply hK1odd
  rw [← hT1, ← hm]
  exact Dvd.dvd.mul_right h2 _

theorem DIEnv.ccF_mem_IV1 (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (h12813f : Lemma12_8_13_five) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hK₁C : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (hK₁N : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁)
    {k : G} (hk : k ∈ k0Sub K₁ D (D.π E.a)) : ccF E.a k ∈ E.I ⊔ V₁ := by
  classical
  have hcomm : ∀ x ∈ zU128 V V₁, ∀ y ∈ zU128 V V₁, x * y = y * x := fun x hx y hy =>
    (mem_centerOf_iff'.1 hy).2 x (zU_le_u128 hx)
  have hIJ : E.I ⊔ V₁ ≤ zU128 V V₁ := sup_le E.hIZ (V₁_le_zU h1222 h12213 E.hs)
  have hKZ : ∀ k' ∈ k0Sub K₁ D (D.π E.a), ∀ z ∈ zU128 V V₁, k' * z * k'⁻¹ ∈ zU128 V V₁ := by
    intro k' hk' z hz
    obtain ⟨-, hkN, -⟩ := mem_k0Sub.1 hk'
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) hkN) z).1 hz
  have htriv : ∀ k' ∈ k0Sub K₁ D (D.π E.a), ∀ z ∈ zU128 V V₁,
      k' * z * k'⁻¹ * z⁻¹ ∈ E.I ⊔ V₁ := by
    intro k' hk' z hz
    obtain ⟨hkK, -, -⟩ := mem_k0Sub.1 hk'
    exact Subgroup.mem_sup_left
      (E.K1_triv h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hkK hz)
  haveI : ((E.I ⊔ V₁).subgroupOf (zU128 V V₁)).Normal := subgroupOf_normal_of_comm hcomm
  obtain ⟨φ, hφ⟩ := hom_quot (K0 := k0Sub K₁ D (D.π E.a)) hcomm hKZ (ccF E.a) (ccF_one E.a)
    (fun k' hk' => ccF_mem_zU E hk') (fun k' hk' l hl => ccF_mul E.a k' l) htriv
  have hsq : ∀ x : k0Sub K₁ D (D.π E.a), φ x ^ 2 = 1 := by
    rintro ⟨y, hy⟩
    rw [hφ y hy, ← QuotientGroup.mk_pow]
    have hu : (⟨ccF E.a y, ccF_mem_zU E hy⟩ : zU128 V V₁) ^ 2 = 1 :=
      Subtype.ext (by simpa using ccF_sq E hy)
    rw [hu]
    rfl
  have hT2 : IsPGroup (2 : ℕ) (T ⊓ k0Sub K₁ D (D.π E.a) : Subgroup G) :=
    E.hcx.hyp.hyp.sylow.1.to_inf_left
  have hS2 : IsPGroup (2 : ℕ)
      ((T ⊓ k0Sub K₁ D (D.π E.a) : Subgroup G).subgroupOf (k0Sub K₁ D (D.π E.a))) :=
    hT2.comap_subtype
  have hSyl := T_inf_K0_odd E h1222 h12213 hK₁N
  have hSA : ((T ⊓ k0Sub K₁ D (D.π E.a)).subgroupOf (k0Sub K₁ D (D.π E.a))) ≤ φ.ker := by
    intro x hx
    obtain ⟨y, hy⟩ := x
    rw [MonoidHom.mem_ker, hφ y hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hyT := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_sup_right (ccF_T_mem_V1 E hyT.1 (mem_k0Sub.1 hyT.2).1)
  have hodd : ∀ x : k0Sub K₁ D (D.π E.a), Odd (orderOf x) → x ∈ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact hom_odd_trivial φ hsq x hx
  have htop := sylow_odd_normal φ.ker ((T ⊓ k0Sub K₁ D (D.π E.a)).subgroupOf
    (k0Sub K₁ D (D.π E.a))) hS2 hSyl hSA hodd
  have hkA : (⟨k, hk⟩ : k0Sub K₁ D (D.π E.a)) ∈ φ.ker := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, hφ k hk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hkA
  exact hkA

theorem DIEnv.ccF_odd_mem_I (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (h12813f : Lemma12_8_13_five) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hK₁C : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    {k : G} (hk : k ∈ k0Sub K₁ D (D.π E.a)) (hodd : Odd (orderOf k)) : ccF E.a k ∈ E.I := by
  classical
  have hcomm : ∀ x ∈ zU128 V V₁, ∀ y ∈ zU128 V V₁, x * y = y * x := fun x hx y hy =>
    (mem_centerOf_iff'.1 hy).2 x (zU_le_u128 hx)
  have hKZ : ∀ k' ∈ k0Sub K₁ D (D.π E.a), ∀ z ∈ zU128 V V₁, k' * z * k'⁻¹ ∈ zU128 V V₁ := by
    intro k' hk' z hz
    obtain ⟨-, hkN, -⟩ := mem_k0Sub.1 hk'
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) hkN) z).1 hz
  have htriv : ∀ k' ∈ k0Sub K₁ D (D.π E.a), ∀ z ∈ zU128 V V₁, k' * z * k'⁻¹ * z⁻¹ ∈ E.I := by
    intro k' hk' z hz
    obtain ⟨hkK, -, -⟩ := mem_k0Sub.1 hk'
    exact E.K1_triv h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hkK hz
  haveI : (E.I.subgroupOf (zU128 V V₁)).Normal := subgroupOf_normal_of_comm hcomm
  obtain ⟨φ, hφ⟩ := hom_quot (K0 := k0Sub K₁ D (D.π E.a)) hcomm hKZ (ccF E.a) (ccF_one E.a)
    (fun k' hk' => ccF_mem_zU E hk') (fun k' hk' l hl => ccF_mul E.a k' l) htriv
  have hsq : ∀ x : k0Sub K₁ D (D.π E.a), φ x ^ 2 = 1 := by
    rintro ⟨y, hy⟩
    rw [hφ y hy, ← QuotientGroup.mk_pow]
    have hu : (⟨ccF E.a y, ccF_mem_zU E hy⟩ : zU128 V V₁) ^ 2 = 1 :=
      Subtype.ext (by simpa using ccF_sq E hy)
    rw [hu]
    rfl
  have hodd' : Odd (orderOf (⟨k, hk⟩ : k0Sub K₁ D (D.π E.a))) := by
    rw [← Subgroup.orderOf_coe]
    exact hodd
  have hφk : φ ⟨k, hk⟩ = 1 := hom_odd_trivial φ hsq _ hodd'
  rw [hφ k hk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hφk
  exact hφk

end Env

end CFSG.Quasithin.H13.C1294
