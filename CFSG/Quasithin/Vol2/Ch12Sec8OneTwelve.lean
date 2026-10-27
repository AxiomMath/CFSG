module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTwelveD
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsInst

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem twelve_of_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {U : Subgroup G}
    (hU : uA V V₁ = U) (D : HatModelU U) (hU4 : 4 < (centerOf U).relIndex U) {a : G}
    (haV : a ∈ V) (haZ : a ∉ V₁) (hG : G11.TheoremG112Fix)
    (hsqtk : IsQuotientOfSQTKTauCeti ↥(D.img (Subgroup.normalizer (V₁ : Set G)))) :
    G101Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
        (D.hat (U ⊓ Subgroup.centralizer (V : Set G) ⊓
          rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
        (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)) (D.img (rconj (centerOf U) g)) ∧
      G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
        (D.hat (U ⊓ Subgroup.centralizer (V : Set G) ⊓
          rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
        (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)) (D.img (rconj (centerOf U) g)) ∧
      G11.G112ConclusionFix D.B (D.img (Subgroup.normalizer (V₁ : Set G)))
        (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)) := by
  subst hU
  have h3 := S.twelve_three hg D hU4 haV haZ
  exact ⟨h3.toG101Hyp, h3, hG D.V D.B _ (D.π a) _ _ _ h3 hsqtk⟩

end Setting

end L128A

namespace L128P

variable {G : Type} [Group G] [Finite G]

theorem uA_eq (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) : L128A.uA V₂ V₁ = u128 V V₁ :=
  (lemma12_8_8_six h1222 hs).symm

theorem four_lt_relIndex (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    4 < (zU128 V V₁).relIndex (u128 V V₁) := by
  obtain ⟨hcard, -, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hn3 : 3 ≤ n := by rcases hs.hyp.n_mem with rfl | rfl | rfl <;> omega
  have hZU : zU128 V V₁ ≤ u128 V V₁ := inf_le_left
  have hVU : V ≤ u128 V V₁ := le_conjClosure V _
  have hNorm : u128 V V₁ ≤ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    fun u hu => normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hu)
  have hsecond : (zU128 V V₁).relIndex (zU128 V V₁ ⊔ V) = (V ⊓ zU128 V V₁).relIndex V := by
    have : ((zU128 V V₁).subgroupOf (u128 V V₁)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNorm
    have h1 := Subgroup.relIndex_sup_left (K := (zU128 V V₁).subgroupOf (u128 V V₁))
      (H := V.subgroupOf (u128 V V₁))
    rw [← Subgroup.subgroupOf_sup hZU hVU, Subgroup.relIndex_subgroupOf (sup_le hZU hVU),
      Subgroup.relIndex_subgroupOf hVU] at h1
    rw [h1, ← Subgroup.inf_relIndex_right, inf_comm]
  have hVV₁ : 4 ≤ V₁.relIndex V := by
    have h1 := Subgroup.relIndex_mul_card V₁ V
    rw [inf_eq_left.2 hs.v1.1, hcard, hV₁2] at h1
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  have hchain := Subgroup.relIndex_mul_relIndex (zU128 V V₁) (zU128 V V₁ ⊔ V) (u128 V V₁)
    le_sup_left (sup_le hZU hVU)
  rw [hsecond, lemma12_8_8_three h1222 h12213 hs] at hchain
  have hne : (zU128 V V₁).relIndex (u128 V V₁) ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_contra hle
  push Not at hle
  have hr1 : (zU128 V V₁ ⊔ V).relIndex (u128 V V₁) = 1 := by
    rcases Nat.lt_or_ge ((zU128 V V₁ ⊔ V).relIndex (u128 V V₁)) 2 with hr | hr
    · have : (zU128 V V₁ ⊔ V).relIndex (u128 V V₁) ≠ 0 := fun h0 => hne (by rw [← hchain, h0,
        mul_zero])
      omega
    · have := Nat.mul_le_mul hVV₁ hr
      omega
  have hUZV : u128 V V₁ ≤ zU128 V V₁ ⊔ V := Subgroup.relIndex_eq_one.mp hr1
  have hcomm : ∀ z ∈ zU128 V V₁, ∀ v ∈ V, z * v = v * z := fun z hz v hv =>
    (Subgroup.mem_centralizer_iff.mp hz.2 v (hVU hv)).symm
  apply hs.nonabelian
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨z, hz, v, hv, hzv⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hcomm (hUZV x.2)
  obtain ⟨z', hz', v', hv', hzv'⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hcomm (hUZV y.2)
  show (x : G) * y = y * x
  rw [← hzv, ← hzv']
  have h1 : z * z' = z' * z := Subgroup.mem_centralizer_iff.mp hz'.2 z hz.1
  have h2 : v * z' = z' * v := (hcomm z' hz' v hv).symm
  have h3 : z * v' = v' * z := hcomm z hz v' hv'
  have h4 : v * v' = v' * v := hab v hv v' hv'
  calc z * v * (z' * v') = z * (v * z') * v' := by group
    _ = z * (z' * v) * v' := by rw [h2]
    _ = (z * z') * (v * v') := by group
    _ = (z' * z) * (v' * v) := by rw [h1, h4]
    _ = z' * (z * v') * v := by group
    _ = z' * (v' * z) * v := by rw [h3]
    _ = z' * v' * (z * v) := by group

theorem T_le_normalizer_w128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    T ≤ Subgroup.normalizer (w128 V V₁ V₂ : Set G) ∧
      T ≤ Subgroup.normalizer (zU128 V V₁ : Set G) := by
  have hA := hs.almostSpecial h1222 h12213
  have hTU : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) := hA.G22_three.2
  refine ⟨fun t ht => ?_, hTU.trans (normalizer_le_normalizer_centerOf _)⟩
  have h1 : t ∈ Subgroup.normalizer (Subgroup.centralizer (V₂ : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _ (hs.v2.2.2 ht)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hTU ht, h1⟩

theorem isQuotientOfSQTK_img {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) (D : HatModelU (u128 V V₁)) :
    IsQuotientOfSQTKTauCeti ↥(D.img (Subgroup.normalizer (V₁ : Set G))) := by
  have hyp := hs.hyp.hyp
  have := hyp.simple
  have hcore := CFSG.QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hP : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := by
    intro hb
    have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ (IsPGroup.of_card hs.v1.2.1)
    rw [hb, le_bot_iff] at h1
    have h2 := hs.v1.2.1
    rw [h1, Subgroup.card_bot] at h2
    norm_num at h2
  exact L1294.isQuotientOfSQTK_img D (le_normalizer_conjClosure V _) (hcore.1 _ hP)

end L128P

open L128P in
theorem lemma12_8_12_hat_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hG : G11.TheoremG112Fix) : Lemma12_8_12_hat := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN a ha haV₁ D
  have S := setting128A h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  exact S.twelve_of_eq ⟨hk, hkN⟩ (uA_eq h1222 hs) D (four_lt_relIndex h1222 h12213 hs) ha haV₁
    hG (isQuotientOfSQTK_img hs D)

end CFSG.Quasithin.H13
