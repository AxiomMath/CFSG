module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneNine
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbs
public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.GH74.M12.HypGroup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsKleinFour

namespace L128P

variable {G : Type} [Group G] [Finite G]

private theorem isKleinFour_of_card_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem sup_inf_centralizer_eq (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) :
    (oTwoUpper (p128 T L V) ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) =
      pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T) := by
  have hKTP : oTwoUpper (p128 T L V) ⊔ T ≤ p128 T L V := sup_le (oTwoUpper_le _) le_p128
  have hKTN : oTwoUpper (p128 T L V) ⊔ T ≤ Subgroup.normalizer (V₂ : Set G) :=
    hKTP.trans (p128_le_normalizer le_rfl hV₂)
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _) (pCoreOf_le_centralizer h1222 h hV₁ hV₂ hle))
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left
    ((le_inf Subgroup.le_normalizer
      (hKTN.trans (normalizer_le_normalizer_centralizer'' V₂))).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    ((isPGroup_centralizer_p128 h1222 h hV₁ hle).to_le (inf_le_inf_right _ hKTP))

theorem autOn_eq_top (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) :
    autOn (oTwoUpper (p128 T L V) ⊔ T) V₂ = ⊤ := by
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ := exists_rotation_mem h1222 h hV₁ hV₂ hle ha ha1 hb hbV₁
  obtain ⟨l, hl, hla, hlb⟩ := exists_transvection_mem h1222 h hV₁ hV₂ hle ha hb hbV₁
  have haV : a ∈ V := hV₁.1 ha
  have hbV : b ∈ V := hV₂.1 hb
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hsq b hbV
  have haV₂ : a ∈ V₂ := hle ha
  have hb1 : b ≠ 1 := fun e => hbV₁ (e ▸ V₁.one_mem)
  have hsel : ∀ {y : G}, y ∈ V₂ → y ≠ 1 → y = a ∨ y = b ∨ y = a * b := fun hy hy1 => by
    rcases eq_of_mem_four hle hV₁2 hV₂4 ha ha1 hbV₁ hb hy with e | e | e | e
    · exact absurd e hy1
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  rw [eq_top_iff]
  intro α _
  have hne1 : ∀ (v : ↥V₂), (v : G) ≠ 1 → ((α v : ↥V₂) : G) ≠ 1 := fun v hv e => hv (by
    have : α v = 1 := Subtype.ext e
    rw [← map_one α] at this
    exact congrArg Subtype.val (α.injective this))
  have hne : ((α ⟨a, haV₂⟩ : ↥V₂) : G) ≠ ((α ⟨b, hb⟩ : ↥V₂) : G) := fun e => hbV₁ (by
    have h1 := congrArg Subtype.val (α.injective (Subtype.ext e))
    simp only at h1
    rw [← h1]
    exact ha)
  obtain ⟨p, hp, hpa, hpb⟩ := exists_conj_pair (X := p128 T L V) (oTwoUpper_le _ hk) hl hka hkb
    hla hlb (hab a haV b hbV) hb2 (hsel (α ⟨a, haV₂⟩).2 (hne1 _ ha1))
    (hsel (α ⟨b, hb⟩).2 (hne1 _ hb1)) hne
  have hpKT : p ∈ oTwoUpper (p128 T L V) ⊔ T := by rw [oTwoUpper_sup_eq h]; exact hp
  have hpN : p ∈ Subgroup.normalizer (V₂ : Set G) := p128_le_normalizer le_rfl hV₂ hp
  refine ⟨⟨p, hpN⟩, hpKT, ?_⟩
  refine MulEquiv.ext fun v => Subtype.ext ?_
  rw [conjAct_coe_apply]
  rcases eq_of_mem_four hle hV₁2 hV₂4 ha ha1 hbV₁ hb v.2 with e | e | e | e
  · have hv : v = 1 := Subtype.ext e
    rw [hv, map_one]
    simp
  · have hv : v = ⟨a, haV₂⟩ := Subtype.ext e
    rw [hv]
    exact hpa
  · have hv : v = ⟨b, hb⟩ := Subtype.ext e
    rw [hv]
    exact hpb
  · have hv : v = ⟨a, haV₂⟩ * ⟨b, hb⟩ := Subtype.ext e
    rw [hv, map_mul]
    show p * (a * b) * p⁻¹ = ((α ⟨a, haV₂⟩ : ↥V₂) : G) * ((α ⟨b, hb⟩ : ↥V₂) : G)
    rw [← hpa, ← hpb]
    group

theorem nonempty_mulEquiv_perm_three (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) :
    Nonempty (OTwoQuot (oTwoUpper (p128 T L V) ⊔ T) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  set KT := oTwoUpper (p128 T L V) ⊔ T with hKT
  have hKTN : KT ≤ Subgroup.normalizer (V₂ : Set G) := by
    rw [hKT, oTwoUpper_sup_eq h]
    exact p128_le_normalizer le_rfl hV₂
  have : IsKleinFour ↥V₂ := isKleinFour_of_card_four hV₂4 fun x => Subtype.ext (by
    simpa using hsq x (hV₂.1 x.2))
  have hcard : Nat.card (OTwoQuot KT) = 6 := by
    have h1 := card_autOn_eq_relIndex hKTN
    rw [autOn_eq_top h1222 h hV₁ hV₂ hle, Subgroup.card_top, kleinFour_automorphism_card,
      sup_inf_centralizer_eq h1222 h hV₁ hV₂ hle] at h1
    have hsub : (pCoreOf 2 KT).subgroupOf KT = CFSG.Open.pCore 2 ↥KT :=
      map_subtype_subgroupOf' (CFSG.Open.pCore 2 ↥KT)
    show (CFSG.Open.pCore 2 ↥KT).index = 6
    rw [← hsub]
    exact h1.symm
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ := exists_rotation_mem h1222 h hV₁ hV₂ hle ha ha1 hb hbV₁
  obtain ⟨l, hl, hla, hlb⟩ := exists_transvection_mem h1222 h hV₁ hV₂ hle ha hb hbV₁
  have hkKT : k ∈ KT := Subgroup.mem_sup_left hk
  have hlKT : l ∈ KT := by rw [hKT, oTwoUpper_sup_eq h]; exact hl
  let π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥KT)
  refine CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hcard
    (π ⟨k, hkKT⟩) (π ⟨l, hlKT⟩) fun hc => ?_
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hc
  have hcmem : (k * l)⁻¹ * (l * k) ∈ pCoreOf 2 KT := ⟨_, hc, rfl⟩
  have hcC := ((sup_inf_centralizer_eq h1222 h hV₁ hV₂ hle).ge hcmem).2
  have hfix := Subgroup.mem_centralizer_iff.mp hcC a (hle ha)
  have hca : ((k * l)⁻¹ * (l * k)) * a * ((k * l)⁻¹ * (l * k))⁻¹ = a := by
    rw [← hfix]
    group
  have e1 : (k * l) * a * (k * l)⁻¹ = b := by
    calc (k * l) * a * (k * l)⁻¹ = k * (l * a * l⁻¹) * k⁻¹ := by group
      _ = b := by rw [hla, hka]
  have e2 : (l * k) * a * (l * k)⁻¹ = a * b := by
    calc (l * k) * a * (l * k)⁻¹ = l * (k * a * k⁻¹) * l⁻¹ := by group
      _ = a * b := by rw [hka, hlb]
  have e3 : a * b = b := by
    calc a * b = (l * k) * a * (l * k)⁻¹ := e2.symm
      _ = (k * l) * (((k * l)⁻¹ * (l * k)) * a * ((k * l)⁻¹ * (l * k))⁻¹) * (k * l)⁻¹ := by
          group
      _ = b := by rw [hca, e1]
  exact ha1 (by
    calc a = (a * b) * b⁻¹ := by group
      _ = b * b⁻¹ := by rw [e3]
      _ = 1 := by group)

theorem inf_centerOf_eq (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    V₂ ⊓ centerOf (L128A.uA V₂ V₁) = V₁ := by
  have hU : L128A.uA V₂ V₁ = u128 V V₁ := (lemma12_8_8_six h1222 hs).symm
  rw [hU]
  refine le_antisymm ?_ (le_inf hs.le (hs.le_centerOf h1222 h12213))
  exact (inf_le_inf_right _ hs.v2.1).trans (lemma12_8_8_three h1222 h12213 hs).le

theorem setting128A (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    L128A.Setting V₂ V₁ (oTwoUpper (p128 T L V)) T where
  hyp := almostSpecialL2Hyp h1222 h12213 hs
  card_V := by simpa using hs.v2.2.1
  card_V₁ := by simpa using hs.v1.2.1
  centralizer := sup_inf_centralizer_eq h1222 hs.hyp hs.v1 hs.v2 hs.le
  sThree := nonempty_mulEquiv_perm_three h1222 hs.hyp hs.v1 hs.v2 hs.le
  inf_centerOf := inf_centerOf_eq h1222 h12213 hs

end L128P

end CFSG.Quasithin.H13
