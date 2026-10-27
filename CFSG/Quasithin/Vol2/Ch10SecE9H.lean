module

public import CFSG.Quasithin.Vol2.Ch10SecE9G
public import CFSG.Quasithin.Vol2.Ch10SecE9D
public import CFSG.Quasithin.Vol2.Ch10SecE9E
public import CFSG.Quasithin.Vol2.Ch10SecE9F

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

omit [Finite G] in
theorem mem_normalizer_of_mem_centralizer {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q}
    {a : Q} (ha : a ∈ Subgroup.centralizer (Y : Set Q)) : a ∈ Subgroup.normalizer (Y : Set Q) :=
  C10P34.mem_normalizer_of_forall_conj_mem fun y hy => by
    rw [← Subgroup.mem_centralizer_iff.mp ha y hy, mul_inv_cancel_right]; exact hy

theorem mem_normalizer_or_witness {X T T₁ : Subgroup G}
    (hc : C10P34.PairCtx H K₁ K₂ φ) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (e₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hXK : X ≤ K₁ ⊔ K₂) (hXO : oTwoUpper X = X) (hX3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT2 : IsPGroup 2 T) (hTH : T ≤ H) (hT₁T : T₁ ≤ T)
    (hTT₁ : T ≤ Subgroup.normalizer (T₁ : Set G))
    (hW : pCoreOf 2 (X ⊔ T ⊓ (K₁ ⊔ K₂)) ≤ T₁ ⊓ (K₁ ⊔ K₂)) {s : G} (hs : s ∈ T)
    (hs₁₂ : K₁.map (MulAut.conj s).toMonoidHom = K₂)
    (hbad : pCoreOf 2 X ≤ pCoreOf 2 (K₁ ⊔ K₂)) {n : G} (hnH : n ∈ H)
    (hnT₁ : n ∈ Subgroup.normalizer (T₁ : Set G)) (hodd : Odd (orderOf n)) :
    n ∈ Subgroup.normalizer (X : Set G) ∨
      (T ⊓ (K₁ ⊔ K₂) ≤ T₁ ∧ ∃ y ∈ K₁ ⊔ K₂, orderOf y = 3 ∧
        y ∈ Subgroup.normalizer (T₁ : Set G) ∧ y ∉ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) := fun k hk => by
    have h1 : k ∈ φ.ker := hk
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hO : ∀ k : ↥(K₁ ⊔ K₂), (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) → φ k = 1 := fun k hk => by
    have h1 : k ∈ φ.ker := by rw [hc.ker, Subgroup.mem_subgroupOf]; exact hk
    exact h1
  obtain ⟨hn₁, hn₂⟩ := hc.fix_of_odd hnH hodd
  have hnK := hc.normal hnH
  obtain ⟨a₁, ha₁, ha₁o⟩ :=
    C10P34.exists_inner_of_pow_eq_one e₁ hodd (C10P34.conjQuot_pow_orderOf hn₁)
  obtain ⟨a₂, ha₂, ha₂o⟩ :=
    C10P34.exists_inner_of_pow_eq_one e₂ hodd (C10P34.conjQuot_pow_orderOf hn₂)
  have hconj : ∀ (z : G) (hz : z ∈ K₁ ⊔ K₂) (hz' : n * z * n⁻¹ ∈ K₁ ⊔ K₂),
      φ ⟨n * z * n⁻¹, hz'⟩ = (a₁ * (φ ⟨z, hz⟩).1 * a₁⁻¹, a₂ * (φ ⟨z, hz⟩).2 * a₂⁻¹) := by
    intro z hz hz'
    rw [hc.app_conj_fix hn₁ hn₂ hz, ← ha₁, ← ha₂]
    rfl
  obtain ⟨hSyl₁, hSyl₂, hSprod⟩ := map_sylow_eq_prod hc.surj hS
  have hXprod := C10P34.map_eq_prod hp5 e₁ e₂ hker hXK hXO hX3 hPX hP hP3
  have hY₁ := card_eq_three_of_pCoreOf_eq_bot hp5 e₁
    (C10P34.fst_ne_bot hp5 e₂ hker hXK hXO hX3 hPX hP hP3) (C10P34.oTwoUpper_map_eq _ hXK hXO)
    (C10P34.pow_three_mem_map _ hXK hX3) (pCoreOf_map_fst_eq_bot hker hO hXK hXprod hbad)
  have hY₂ := card_eq_three_of_pCoreOf_eq_bot hp5 e₂
    (C10P34.snd_ne_bot hp5 e₁ hker hXK hXO hX3 hPX hP hP3) (C10P34.oTwoUpper_map_eq _ hXK hXO)
    (C10P34.pow_three_mem_map _ hXK hX3) (pCoreOf_map_snd_eq_bot hker hO hXK hXprod hbad)
  have hSX : T ⊓ (K₁ ⊔ K₂) ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have hSY₁ := C10P34.map_le_normalizer_map ((MonoidHom.fst _ _).comp φ) hSX hXK
  have hSY₂ := C10P34.map_le_normalizer_map ((MonoidHom.snd _ _).comp φ) hSX hXK
  have hRS : T₁ ⊓ (K₁ ⊔ K₂) ≤ T ⊓ (K₁ ⊔ K₂) := inf_le_inf_right _ hT₁T
  have hnR : ∀ r ∈ T₁ ⊓ (K₁ ⊔ K₂), n * r * n⁻¹ ∈ T₁ ⊓ (K₁ ⊔ K₂) := fun r hr =>
    ⟨(Subgroup.mem_normalizer_iff.mp hnT₁ r).mp hr.1, conj_mem_of_mem_normalizer hnK hr.2⟩
  have hZS₁ : (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _) ≤
      ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) := by
    rintro u ⟨w, hw, hwu⟩
    exact ⟨w, hRS hw, by rw [MonoidHom.comp_apply, hwu]; rfl⟩
  have hZS₂ : (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _) ≤
      ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) := by
    rintro u ⟨w, hw, hwu⟩
    exact ⟨w, hRS hw, by rw [MonoidHom.comp_apply, hwu]; rfl⟩
  have hab₁ := (isKleinFour_of_sylow h8 e₁ hSyl₁).isMulCommutative
  have hab₂ := (isKleinFour_of_sylow h8 e₂ hSyl₂).isMulCommutative
  have hCZ₁ : ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) ⊓
      Subgroup.centralizer
        ((((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) : Subgroup _) : Set _) ≤
      (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _) := by
    intro u hu
    have hu' := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans le_sup_right)
      (sup_le (fun y hy => C10P34.mem_normalizer_of_forall_conj_mem fun v hv => by
          rw [Subgroup.mem_centralizer_iff.mp hv.2 y hy, mul_inv_cancel_right]; exact hv)
        (fun t ht => C10P34.mem_normalizer_of_forall_conj_mem fun v hv => by
          have hc' := congrArg Subtype.val (isMulCommutative_iff.mp hab₁ ⟨t, ht⟩ ⟨v, hv.1⟩)
          simp only [Subgroup.coe_mul] at hc'
          rw [hc', mul_inv_cancel_right]; exact hv))
      (hSyl₁.2.1.to_le inf_le_left) hu
    obtain ⟨w, hw, hwu⟩ := inl_mem_map_pCoreOf hc.surj hker hS hXK hu'
    exact ⟨w, hW hw, hwu⟩
  have hCZ₂ : ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) ⊓
      Subgroup.centralizer
        ((((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) : Subgroup _) : Set _) ≤
      (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _) := by
    intro u hu
    have hu' := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans le_sup_right)
      (sup_le (fun y hy => C10P34.mem_normalizer_of_forall_conj_mem fun v hv => by
          rw [Subgroup.mem_centralizer_iff.mp hv.2 y hy, mul_inv_cancel_right]; exact hv)
        (fun t ht => C10P34.mem_normalizer_of_forall_conj_mem fun v hv => by
          have hc' := congrArg Subtype.val (isMulCommutative_iff.mp hab₂ ⟨t, ht⟩ ⟨v, hv.1⟩)
          simp only [Subgroup.coe_mul] at hc'
          rw [hc', mul_inv_cancel_right]; exact hv))
      (hSyl₂.2.1.to_le inf_le_left) hu
    obtain ⟨w, hw, hwu⟩ := inr_mem_map_pCoreOf hc.surj hker hS hXK hu'
    exact ⟨w, hW hw, hwu⟩
  have haZ₁ : ∀ u ∈ (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _),
      a₁ * u * a₁⁻¹ ∈ (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap
        (MonoidHom.inl _ _) := by
    rintro u ⟨⟨w, hwK⟩, hw, hwu⟩
    have hw' := conj_mem_of_mem_normalizer hnK hwK
    refine ⟨⟨n * w * n⁻¹, hw'⟩, hnR w hw, ?_⟩
    rw [hconj w hwK hw', hwu]
    simp
  have haZ₂ : ∀ u ∈ (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _),
      a₂ * u * a₂⁻¹ ∈ (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap
        (MonoidHom.inr _ _) := by
    rintro u ⟨⟨w, hwK⟩, hw, hwu⟩
    have hw' := conj_mem_of_mem_normalizer hnK hwK
    refine ⟨⟨n * w * n⁻¹, hw'⟩, hnR w hw, ?_⟩
    rw [hconj w hwK hw', hwu]
    simp
  have hsH := hTH hs
  have hs₂₁ : K₂.map (MulAut.conj s).toMonoidHom = K₁ := by
    rcases hc.fix_or_swap hsH with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans hs₁₂) hc.ne
    · exact h2
  have hsR : ∀ r ∈ T₁ ⊓ (K₁ ⊔ K₂), s * r * s⁻¹ ∈ T₁ ⊓ (K₁ ⊔ K₂) := fun r hr =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hTT₁ hs) r).mp hr.1,
      conj_mem_of_mem_normalizer (hc.normal hsH) hr.2⟩
  have hcard :
      Nat.card (((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) =
      Nat.card (((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) := by
    rw [(isKleinFour_of_sylow h8 e₁ hSyl₁).card_four,
      (isKleinFour_of_sylow h8 e₂ hSyl₂).card_four]
  have hOT₁ : pCoreOf 2 (K₁ ⊔ K₂) ≤ T₁ := fun x hx =>
    (hW (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS).trans le_sup_right)
      ((sup_le hXK inf_le_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hx)).1
  by_cases hβ : ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ) ≤
      (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inl _ _)
  · have hβ₂ := le_comap_inr_of_le_comap_inl hc hs₁₂ hs₂₁ hRS inf_le_right hsR hcard hβ
    have hST₁ : T ⊓ (K₁ ⊔ K₂) ≤ T₁ := by
      intro t ht
      have hφt : φ ⟨t, ht.2⟩ ∈ ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ :=
        ⟨⟨t, ht.2⟩, ht, rfl⟩
      rw [hSprod] at hφt
      obtain ⟨w₁, hw₁, hw₁u⟩ := hβ hφt.1
      obtain ⟨w₂, hw₂, hw₂u⟩ := hβ₂ hφt.2
      have hφw : φ (w₁ * w₂) = φ ⟨t, ht.2⟩ := by
        rw [map_mul, hw₁u, hw₂u]
        exact Prod.ext (by simp) (by simp)
      have hq : ((w₁ * w₂ : ↥(K₁ ⊔ K₂)) : G)⁻¹ * t ∈ pCoreOf 2 (K₁ ⊔ K₂) :=
        hker ((w₁ * w₂)⁻¹ * ⟨t, ht.2⟩) (by rw [map_mul, map_inv, hφw, inv_mul_cancel])
      have e : t = (w₁ : G) * w₂ * (((w₁ * w₂ : ↥(K₁ ⊔ K₂)) : G)⁻¹ * t) := by
        simp only [Subgroup.coe_mul]; group
      rw [e]
      exact T₁.mul_mem (T₁.mul_mem (Subgroup.mem_subgroupOf.mp hw₁).1
        (Subgroup.mem_subgroupOf.mp hw₂).1) (hOT₁ hq)
    have ha₁S := C10P34.mem_normalizer_of_forall_conj_mem fun u hu => hZS₁ (haZ₁ u (hβ hu))
    have ha₂S := C10P34.mem_normalizer_of_forall_conj_mem fun u hu => hZS₂ (haZ₂ u (hβ₂ hu))
    by_cases htriv : a₁ = 1 ∧ a₂ = 1
    · left
      obtain ⟨rfl, rfl⟩ := htriv
      exact mem_normalizer_of_inner hc hp5 e₁ e₂ hXK hXO hX3 hPX hP hP3 hS hTX hnK hconj
        (Subgroup.one_mem _) (Subgroup.one_mem _)
    · right
      exact ⟨hST₁, exists_witness hc h8 e₁ e₂ hXK hY₁ hY₂ hXprod hS hTX hT2 hTH hT₁T hST₁
        hnH hnT₁ hconj ha₁S ha₂S ha₁o ha₂o htriv⟩
  · left
    have hβ₂ : ¬ ((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ) ≤
        (((T₁ ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map φ).comap (MonoidHom.inr _ _) := fun h =>
      hβ (le_comap_inl_of_le_comap_inr hc hs₁₂ hs₂₁ hRS inf_le_right hsR hcard h)
    have ha₁C := mem_centralizer_of_normalizes h8 e₁ hSyl₁ hY₁ hSY₁ hCZ₁ hZS₁
      (fun h => hβ (h ▸ le_rfl)) ha₁o haZ₁
    have ha₂C := mem_centralizer_of_normalizes h8 e₂ hSyl₂ hY₂ hSY₂ hCZ₂ hZS₂
      (fun h => hβ₂ (h ▸ le_rfl)) ha₂o haZ₂
    exact mem_normalizer_of_inner hc hp5 e₁ e₂ hXK hXO hX3 hPX hP hP3 hS hTX hnK hconj
      (mem_normalizer_of_mem_centralizer ha₁C) (mem_normalizer_of_mem_centralizer ha₂C)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
