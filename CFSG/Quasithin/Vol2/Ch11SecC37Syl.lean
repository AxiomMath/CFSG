module

public import CFSG.Quasithin.Vol2.Ch11SecC37Set
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11SecCB213
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

omit [Finite G] in
theorem hStar_le_normalizer_kStar (T H : Subgroup G) :
    autOn H (VZ T H) ≤
      Subgroup.normalizer (autOn (oTwoUpper H) (VZ T H) : Set (MulAut ↥(VZ T H))) := by
  intro x hx
  have hc := autOn_normal_of (U := VZ T H) (le_normalizer_oTwoUpper H)
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
  have := hc x⁻¹ ((autOn H (VZ T H)).inv_mem hx) _ hk
  simpa [mul_assoc] using this

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem hStar_two : ∀ h ∈ autOn H (VZ T H), ∃ e : ℕ, h ^ 2 ^ e ∈ autOn (oTwoUpper H) (VZ T H) := by
  refine autOn_two_of (K_le_normalizer_VZ T H) fun y hy => ?_
  have hy' : y ∈ oTwoUpper H ⊔ T := s.sup_eq.ge hy
  obtain ⟨e, he⟩ := two_of_sup s.hyp.fsu.sylow.1 ((s.T_le).trans (le_normalizer_oTwoUpper H)) y hy'
  exact ⟨e, Subgroup.mem_sup_left he⟩

theorem sq_eq_one_VZ : ∀ w : ↥(VZ T H), w ^ 2 = 1 := fun w =>
  Subtype.ext (by simpa using s.isElemAbelian_VZ.2 w w.2)

theorem aStar_sylow [IsMulCommutative ↥(VZ T H)] (hAS : FactAStarSylow) (hF : SecA.NatFacts)
    (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2)
    (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    QuasithinUnique.IsSylowTwoOf (autOn (conjSubgroup (fsuV T I) g) (VZ T H))
      (autOn (oTwoUpper H) (VZ T H)) := by
  obtain ⟨F, _, _, hF', he⟩ := s.kStar_equiv h1135 h1136
  exact hAS ↥(VZ T H) s.sq_eq_one_VZ n s.two_le _ _ (autOn_le_autOn_of_le (oTwoUpper_le H))
    (hStar_le_normalizer_kStar T H) ⟨F, inferInstance, inferInstance, hF', he⟩ s.hStar_two
    s.pCore_hStar _ (s.aStar_mem hF h1102 hG2 h1122 h1134)

theorem card_aStar [IsMulCommutative ↥(VZ T H)] (hAS : FactAStarSylow) (hF : SecA.NatFacts)
    (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2)
    (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    Nat.card ↥(autOn (conjSubgroup (fsuV T I) g) (VZ T H)) = 2 ^ n := by
  have hS := s.aStar_sylow hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  obtain ⟨F, _, _, hF', ⟨e⟩⟩ := s.kStar_equiv h1135 h1136
  have hK : Nat.card ↥(autOn (oTwoUpper H) (VZ T H)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF']
  obtain ⟨a, ha⟩ := hS.2.1.exists_card_eq
  have hidx := Subgroup.card_mul_index
    ((autOn (conjSubgroup (fsuV T I) g) (VZ T H)).subgroupOf (autOn (oTwoUpper H) (VZ T H)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ha, hK] at hidx
  have hodd : Odd ((autOn (conjSubgroup (fsuV T I) g) (VZ T H)).subgroupOf
      (autOn (oTwoUpper H) (VZ T H))).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.2.2)
  have hodd2 : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact SecA.odd_two_pow_sub_one (by have := s.two_le; omega)
  have := SecA.eq_of_two_pow_mul_odd hodd hodd2 hidx
  rw [ha, this]

theorem iSup_map_fixV_eq_top [IsMulCommutative ↥(VZ T H)] :
    (⨆ x ∈ autOn (oTwoUpper H) (VZ T H),
      (fixV (autOn (conjSubgroup (fsuV T I) g) (VZ T H))).map
        (x : MulAut ↥(VZ T H)).toMonoidHom) = ⊤ := by
  set S := ⨆ x ∈ autOn (oTwoUpper H) (VZ T H),
      (fixV (autOn (conjSubgroup (fsuV T I) g) (VZ T H))).map
        (x : MulAut ↥(VZ T H)).toMonoidHom with hS
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    s.T_le.trans (le_normalizer_oTwoUpper H)
  have key : VZ T H ≤ S.map (VZ T H).subtype := by
    refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_of_le_normalizer hTK (s.sup_eq.ge hh)
    have htz : t * z * t⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp
        ((Z_le_center T hz).2) t ht
      rw [this, mul_inv_cancel_right]
    have hzV : z ∈ VZ T H := Z_le_VZ T H hz
    have hkV : k ∈ Subgroup.normalizer (VZ T H : Set G) := K_le_normalizer_VZ T H hk
    have hzfix : (⟨z, hzV⟩ : ↥(VZ T H)) ∈ fixV (autOn (conjSubgroup (fsuV T I) g) (VZ T H)) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hx
      apply Subtype.ext
      rw [coe_conjAct_apply]
      have := Subgroup.mem_centralizer_iff.mp
        ((Z_le_center T hz).2) a (s.hAT ha)
      rw [this, mul_inv_cancel_right]
    have hmem : conjAct (VZ T H) ⟨k, hkV⟩ ⟨z, hzV⟩ ∈ S :=
      (le_iSup₂_of_le (conjAct (VZ T H) ⟨k, hkV⟩) (conjAct_mem_autOn (K_le_normalizer_VZ T H) hk)
        le_rfl : _ ≤ S) ⟨_, hzfix, rfl⟩
    refine ⟨_, hmem, ?_⟩
    rw [Subgroup.coe_subtype, coe_conjAct_apply]
    show k * z * k⁻¹ = (k * t) * z * (k * t)⁻¹
    rw [mul_inv_rev, show k * t * z * (t⁻¹ * k⁻¹) = k * (t * z * t⁻¹) * k⁻¹ by group, htz]
  rw [eq_top_iff]
  intro v _
  obtain ⟨w, hw, hwv⟩ := key v.2
  rw [show v = w from Subtype.ext hwv.symm]
  exact hw

theorem kStar_decomposition [IsMulCommutative ↥(VZ T H)] (hG16 : ASInputs.AS_G_1_6)
    (hAS : FactAStarSylow) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    ∃ (k : ℕ) (W : Fin k → Subgroup ↥(VZ T H)),
      (∀ i, fixV (autOn (oTwoUpper H) (VZ T H)) ≤ W i) ∧
      (∀ i, W i ⊓ (fixV (autOn (oTwoUpper H) (VZ T H)) ⊔ ⨆ (j : Fin k) (_ : j ≠ i), W j) =
        fixV (autOn (oTwoUpper H) (VZ T H))) ∧
      (fixV (autOn (oTwoUpper H) (VZ T H)) ⊔ ⨆ i, W i) = ⊤ ∧
      ∀ i, BinaryNaturalSL (autOn (oTwoUpper H) (VZ T H)) (W i)
        (fixV (autOn (oTwoUpper H) (VZ T H))) 2 n := by
  have hS := s.aStar_sylow hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  have hcard := s.card_aStar hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  have hA := s.aStar_mem hF h1102 hG2 h1122 h1134
  obtain ⟨F, _, _, hF', he⟩ := s.kStar_equiv h1135 h1136
  refine hG16 ↥(VZ T H) s.sq_eq_one_VZ _ _ n s.hyp.one_lt
    ⟨F, inferInstance, inferInstance, hF', he⟩ hS s.iSup_map_fixV_eq_top fun r hr hr1 => ?_
  have hr2 : r ^ 2 = 1 := hA.2.2.1.2 r hr
  have hzc : Nat.card ↥(Subgroup.zpowers r) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hr2 hr1
  have hle : Subgroup.zpowers r ≤ autOn (conjSubgroup (fsuV T I) g) (VZ T H) :=
    Subgroup.zpowers_le.mpr hr
  refine hA.2.2.2 _ hle ?_
  have hidx : (Subgroup.zpowers r).relIndex (autOn (conjSubgroup (fsuV T I) g) (VZ T H)) =
      2 ^ (n - 1) := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers r)
      (autOn (conjSubgroup (fsuV T I) g) (VZ T H))
    rw [inf_eq_left.mpr hle, hcard, hzc] at h1
    have hn : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      have := s.two_le
      omega
    rw [hn] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  rw [E3.mQuot, hidx, padicValNat.prime_pow]
  have := s.two_le
  omega

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
