module

public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Small

variable {M : Type*} [Group M]

theorem isPGroup_zpowers_of_pow {x : M} {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubmonoidClass.mk_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {b x : M} (hb : b ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers b) : x = 1 ∨ x = b ∨ x = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb
  have hk : b ^ k = b ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3, zpow_add, zpow_mul]
    rw [h3, one_zpow, one_mul]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h3' : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hb2 : b ^ (2 : ℤ) = b⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact h3
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    left
    rw [hk, h, zpow_one]
  · right
    right
    rw [hk, h, hb2]

end Small

section Points

variable {G : Type} [Group G] [Finite G]

theorem card_zpowers_sup_eq_nine {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {x y : G} (hxA : x ∈ A) (hyA : y ∈ A) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.zpowers y ⊔ Subgroup.zpowers x : Subgroup G) = 9 := by
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcomm' : ∀ u ∈ Subgroup.zpowers y, ∀ v ∈ Subgroup.zpowers x, u * v = v * u :=
    fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr hyA hu) v (Subgroup.zpowers_le.mpr hxA hv)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm'
  rw [Sec13.zpowers_inf_eq_bot (hA.2 y hyA) hyx, Subgroup.card_bot, mul_one,
    Sec13.card_zpowers_of_pow_three (hA.2 y hyA) hy1,
    Sec13.card_zpowers_of_pow_three (hA.2 x hxA) hx1] at hcard
  exact hcard

theorem not_mem_of_center_eq_bot {a : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) : a ∉ K := by
  intro haK
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  set a' : K := ⟨a, haK⟩ with ha'
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 K) a' ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKa k.2))
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hθ := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hdvd := Subgroup.orderOf_dvd_natCard _ hcen
  have ha'3 : orderOf a' = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime ha3 ha1
  rw [ha'3] at hdvd
  exact hθ hdvd

end Points

section Transvections

variable {G : Type} [Group G] [Finite G]

theorem mem_transvectionGroup_of_mem_wStar (h45 : Sec4.Item4_5)
    (hK2 : KFacts.KS12NormalizerMoves) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {σ : MulAut A} (hσ : σ ∈ Sec13.wStar A) {k : ℕ} (hk : σ ^ 3 ^ k = 1) :
    σ ∈ transvectionGroup A ⟨c, h.mem_A⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hW := normalizer_le_of_sec12StdBar_of_list h45 hK2 h hty
  obtain ⟨P, hP, hPB⟩ := h.exists_sylow
  obtain ⟨hPaut, -⟩ := autIn_eq_transvectionGroup_bar h45 h hZ (fun T hT hT9 hZT =>
    hK2 _ (isQuasisimple_thetaQuot_of_mem h.mem_thetaComponentsAt) hty T hT hT9 hZT) hP hPB
  set T := transvectionGroup A ⟨c, h.mem_A⟩ with hTdef
  have hPW : IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) := by
    rw [← inf_eq_left.mpr hW]
    exact hP
  have hTsyl : IsSylowOf 3 T (Sec13.wStar A) :=
    hPaut ▸ Sec13.Holds134.isSylowOf_autIn_wStar hPW
  have hTn : ∀ g ∈ Sec13.wStar A, ∀ τ ∈ T, g * τ * g⁻¹ ∈ T := by
    intro g hg τ hτ
    obtain ⟨w, hwN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hg
    refine Sec13.Holds134.conj_mem (fun y => ?_) hτ
    rw [mem_zpowers_subtype_iff, mem_zpowers_subtype_iff, Sec4.normalizerMonoidHom_apply_coe]
    exact Subgroup.mem_normalizer_iff.mp (hW hwN) y
  have hσp : IsPGroup 3 ((Subgroup.zpowers σ).subgroupOf (Sec13.wStar A)) :=
    (isPGroup_zpowers_of_pow hk).comap_subtype
  obtain ⟨Q, hQ⟩ := hσp.exists_le_sylow
  have hQsyl : IsSylowOf 3 ((Q : Subgroup (Sec13.wStar A)).map (Sec13.wStar A).subtype)
      (Sec13.wStar A) := ⟨Q, rfl⟩
  obtain ⟨g, hgW, hg⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hTsyl hQsyl
  have hσQ : σ ∈ (Q : Subgroup (Sec13.wStar A)).map (Sec13.wStar A).subtype :=
    ⟨⟨σ, hσ⟩, hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers σ)), rfl⟩
  have h1 := hTn g hgW _ ((hg σ).mp hσQ)
  simpa [mul_assoc] using h1

theorem card_le_three_of_le_transvectionGroup {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A)
    (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hca : c ∉ Subgroup.zpowers a)
    {S : Subgroup (MulAut A)} (hST : S ≤ transvectionGroup A ⟨c, hcA⟩)
    (hSa : ∀ σ ∈ S, σ ⟨a, haA⟩ = ⟨a, haA⟩) : Nat.card S ≤ 3 := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  set D := Subgroup.zpowers c ⊔ Subgroup.zpowers a with hD
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr haA)
  have hD9 : Nat.card D = 9 := by
    have hcomm' : ∀ u ∈ Subgroup.zpowers c, ∀ v ∈ Subgroup.zpowers a, u * v = v * u :=
      fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr hcA hu) v (Subgroup.zpowers_le.mpr haA hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm'
    rw [Sec13.zpowers_inf_eq_bot hc3 hca, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three ha3 ha1] at hcard
    exact hcard
  obtain ⟨y, hyA, hyD⟩ : ∃ y ∈ A, y ∉ D := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ≤ D from hcon)
    omega
  have hAy : A = Subgroup.zpowers y ⊔ D :=
    (eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hyA) hDA) le_sup_right hD9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hyD).symm
  have hmem : ∀ σ ∈ S, σ ∈ Sec13.transvAxis A D := by
    intro σ hσ
    have hσT := hST hσ
    refine ⟨fun z hz => ?_, fun z => ?_⟩
    · have hle : D ≤ (MonoidHom.eqLocus (σ : A →* A) (MonoidHom.id A)).map A.subtype :=
        sup_le (Subgroup.zpowers_le.mpr ⟨⟨c, hcA⟩, hσT.1, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨⟨a, haA⟩, hSa σ hσ, rfl⟩)
      obtain ⟨z', hz', hzz⟩ := hle hz
      have : z' = z := Subtype.ext hzz
      rw [← this]
      exact hz'
    · exact Subgroup.mem_sup_left (mem_zpowers_subtype_iff.mp (hσT.2 z))
  set y' : A := ⟨y, hyA⟩
  let f : S → Subgroup.zpowers (⟨c, hcA⟩ : A) := fun σ =>
    ⟨(σ : MulAut A) y' * y'⁻¹, (hST σ.2).2 y'⟩
  have hf : Function.Injective f := by
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ hστ
    have h1 : σ y' = τ y' := by
      have := congrArg Subtype.val hστ
      simpa [f] using this
    exact Subtype.ext (Sec13.transvAxis_ext hA hyA hAy (hmem σ hσ) (hmem τ hτ) h1)
  have hc'3 : orderOf (⟨c, hcA⟩ : A) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hc3 hc1
  calc Nat.card S ≤ Nat.card (Subgroup.zpowers (⟨c, hcA⟩ : A)) :=
        Nat.card_le_card_of_injective f hf
    _ = 3 := by rw [Nat.card_zpowers, hc'3]

omit [Finite G] in
theorem mem_of_mem_autIn_of_ne_one {A K : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {c : G} (hcA : c ∈ A) {σ : MulAut A}
    (hσK : σ ∈ Sec4.autIn K A) (hσT : σ ∈ transvectionGroup A ⟨c, hcA⟩) (hσ1 : σ ≠ 1) :
    c ∈ K := by
  obtain ⟨g, hgN, hgK, rfl⟩ := Sec4.mem_autIn_iff.mp hσK
  obtain ⟨x, hx⟩ : ∃ x : A, A.normalizerMonoidHom ⟨g, hgN⟩ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (MulEquiv.ext hcon)
  have huc : g * x * g⁻¹ * (x : G)⁻¹ ∈ Subgroup.zpowers c := by
    have := mem_zpowers_subtype_iff.mp (hσT.2 x)
    simpa [Sec4.normalizerMonoidHom_apply_coe] using this
  have hu1 : g * x * g⁻¹ * (x : G)⁻¹ ≠ 1 := by
    intro h1
    apply hx
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    rw [mul_inv_eq_one] at h1
    exact h1
  have huK : g * x * g⁻¹ * (x : G)⁻¹ ∈ K := by
    have h1 : (x : G) * g⁻¹ * (x : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hAK x.2) _).mp (K.inv_mem hgK)
    have e : g * x * g⁻¹ * (x : G)⁻¹ = g * ((x : G) * g⁻¹ * (x : G)⁻¹) := by group
    rw [e]
    exact K.mul_mem hgK h1
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hc3 huc with h | h | h
  · exact absurd h hu1
  · rw [← h]
    exact huK
  · have : c = (g * x * g⁻¹ * (x : G)⁻¹)⁻¹ := by rw [h, inv_inv]
    rw [this]
    exact K.inv_mem huK

end Transvections

section PowSix

variable {G : Type} [Group G] [Finite G]

theorem pow_six_eq_one {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) {σ : MulAut A} (hσa : σ ⟨a, haA⟩ = ⟨a, haA⟩)
    (hσc : ((σ ⟨c, hcA⟩ : A) : G) ∈ Subgroup.zpowers c) : σ ^ 6 = 1 := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcommA : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  set c' : A := ⟨c, hcA⟩ with hc'
  set a' : A := ⟨a, haA⟩ with ha'
  set D := Subgroup.zpowers c ⊔ Subgroup.zpowers a with hD
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr haA)
  have hD9 : Nat.card D = 9 := by
    have hcomm' : ∀ u ∈ Subgroup.zpowers c, ∀ v ∈ Subgroup.zpowers a, u * v = v * u :=
      fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr hcA hu) v (Subgroup.zpowers_le.mpr haA hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm'
    rw [Sec13.zpowers_inf_eq_bot hc3 hca, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three ha3 ha1] at hcard
    exact hcard
  have hσc' : σ c' = c' ∨ σ c' = c'⁻¹ := by
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hc3 hσc with h | h | h
    · exfalso
      have h1 : σ c' = 1 := Subtype.ext h
      rw [map_eq_one_iff _ σ.injective] at h1
      exact hc1 (congrArg Subtype.val h1)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hσ2c : (σ ^ 2) c' = c' := by
    rw [pow_two, MulAut.mul_apply]
    rcases hσc' with h | h
    · rw [h, h]
    · rw [h, map_inv, h, inv_inv]
  have hσ2a : (σ ^ 2) a' = a' := by
    rw [pow_two, MulAut.mul_apply, hσa, hσa]
  have hσD : ∀ z : A, (z : G) ∈ D → ((σ z : A) : G) ∈ D := by
    intro z hz
    have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
      ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from hcomm _ (hDA u.2) _ (hDA v.2))⟩⟩,
        fun u hu => hA.2 u (hDA hu)⟩
    obtain ⟨i, -, b, hb, hzb⟩ := Sec13.exists_pow_mul_of_mem hDe
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) rfl hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hz' : z = c' ^ i * a' ^ j := Subtype.ext (by simp [hzb, c', a'])
    rw [hz', map_mul, map_pow, map_zpow, hσa]
    rcases hσc' with h | h
    · rw [h]
      simpa [c', a'] using D.mul_mem (D.pow_mem (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers c)) i) (D.zpow_mem (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers a)) j)
    · rw [h]
      simpa [c', a'] using D.mul_mem (D.pow_mem (D.inv_mem (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers c))) i) (D.zpow_mem (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers a)) j)
  have hfix : ∀ z : A, (z : G) ∈ D → (σ ^ 2) z = z := by
    intro z hz
    have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
      ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from hcomm _ (hDA u.2) _ (hDA v.2))⟩⟩,
        fun u hu => hA.2 u (hDA hu)⟩
    obtain ⟨i, -, b, hb, hzb⟩ := Sec13.exists_pow_mul_of_mem hDe
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) rfl hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hz' : z = c' ^ i * a' ^ j := Subtype.ext (by simp [hzb, c', a'])
    rw [hz', map_mul, map_pow, map_zpow, hσ2c, hσ2a]
  obtain ⟨y, hyA, hyD⟩ : ∃ y ∈ A, y ∉ D := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ≤ D from hcon)
    omega
  have hAy : A = Subgroup.zpowers y ⊔ D :=
    (eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hyA) hDA) le_sup_right hD9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hyD).symm
  set y' : A := ⟨y, hyA⟩ with hy'
  obtain ⟨i, hi3, d, hdD, hσy⟩ := Sec13.exists_pow_mul_of_mem hA hyA hAy (σ y').2
  have hdA : d ∈ A := hDA hdD
  set d' : A := ⟨d, hdA⟩ with hd'
  have hσy' : σ y' = y' ^ i * d' := Subtype.ext (by simp [hσy, y', d'])
  have hσd : ((σ d' : A) : G) ∈ D := hσD d' hdD
  have key : ∀ w : A, (((y' * w : A)) : G) * y⁻¹ = w := fun w => by
    show y * (w : G) * y⁻¹ = w
    rw [hcomm y hyA _ w.2, mul_inv_cancel_right]
  have hτy : ((((σ ^ 2) y' : A) : G)) * y⁻¹ ∈ D := by
    interval_cases i
    · exfalso
      apply hyD
      let f : D → D := fun z => ⟨σ ⟨z, hDA z.2⟩, hσD ⟨z, hDA z.2⟩ z.2⟩
      have hf : Function.Injective f := by
        intro u v huv
        have h1 : ((σ ⟨u, hDA u.2⟩ : A) : G) = ((σ ⟨v, hDA v.2⟩ : A) : G) :=
          congrArg (fun w : D => (w : G)) huv
        have h2 : σ ⟨u, hDA u.2⟩ = σ ⟨v, hDA v.2⟩ := Subtype.ext h1
        have h3 : (u : G) = v := congrArg (fun w : A => (w : G)) (σ.injective h2)
        exact Subtype.ext h3
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hf) ⟨d, hdD⟩
      have hz1 : ((σ ⟨z, hDA z.2⟩ : A) : G) = d := congrArg (fun w : D => (w : G)) hz
      have hz' : σ ⟨z, hDA z.2⟩ = d' := Subtype.ext hz1
      have h4 : y' = ⟨z, hDA z.2⟩ := σ.injective (by rw [hσy', pow_zero, one_mul, hz'])
      have h5 : y = (z : G) := congrArg Subtype.val h4
      rw [h5]
      exact z.2
    · have h : (σ ^ 2) y' = y' * (d' * σ d') := by
        rw [pow_two, MulAut.mul_apply, hσy', pow_one, map_mul, hσy', pow_one, mul_assoc]
      rw [h, key]
      exact D.mul_mem hdD hσd
    · have hy3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 y hyA)
      have h1 : (y' ^ 2 * d') ^ 2 = y' * d' ^ 2 := by
        rw [Commute.mul_pow (hcommA _ _) 2, ← pow_mul,
          show 2 * 2 = 3 + 1 by norm_num, pow_add, hy3, one_mul, pow_one]
      have h : (σ ^ 2) y' = y' * (d' ^ 2 * σ d') := by
        rw [pow_two σ, MulAut.mul_apply, hσy', map_mul, map_pow, hσy', h1, mul_assoc]
      rw [h, key]
      exact D.mul_mem (by simpa using D.pow_mem hdD 2) hσd
  have hτ : σ ^ 2 ∈ Sec13.transvAxis A D := Sec13.mem_transvAxis_of hA hyA hAy hfix hτy
  have h3 := Sec13.transvAxis_pow_three hA hτ
  rw [← pow_mul] at h3
  exact h3

theorem pow_six_eq_one_of_mem_autIn {A K : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {σ : MulAut A} (hσ : σ ∈ Sec4.autIn K A) : σ ^ 6 = 1 := by
  obtain ⟨g, hgN, hgK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  refine pow_six_eq_one hA h27 haA hcA ha1 hc1 hca ?_ ?_
  · apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hKa hgK)
    rw [hga, mul_inv_cancel_right]
  · rw [Sec4.normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hW hgN) c).mp (Subgroup.mem_zpowers c)

theorem not_orderOf_eq_four {A K : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (σ : Sec4.autIn K A) : orderOf σ ≠ 4 := by
  intro h4
  have h6 := pow_six_eq_one_of_mem_autIn hA h27 haA hcA ha1 hc1 hca hKa hW σ.2
  have h6' : σ ^ 6 = 1 := Subtype.ext (by simpa using h6)
  have := orderOf_dvd_of_pow_eq_one h6'
  rw [h4] at this
  norm_num at this

end PowSix

section Orders

variable {X : Type*} [Group X]

theorem exists_orderOf_eq_four_of_quaternion (e : X ≃* QuaternionGroup 2) :
    ∃ x : X, orderOf x = 4 :=
  ⟨e.symm (QuaternionGroup.a 1), by rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]⟩

theorem exists_orderOf_eq_four_of_sl23 (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    ∃ x : X, orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), orderOf M = 4 :=
    ⟨⟨!![0, 2; 1, 0], by decide⟩, orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)⟩
  exact ⟨e.symm M, (MulEquiv.orderOf_eq e.symm M).trans hM⟩

theorem exists_orderOf_eq_four_of_zmod4 (e : X ≃* Multiplicative (ZMod 4)) :
    ∃ x : X, orderOf x = 4 :=
  ⟨e.symm (Multiplicative.ofAdd 1), by
    rw [MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]⟩

theorem exists_ne_one_pow_three_of_zmod3 (e : X ≃* Multiplicative (ZMod 3)) :
    ∃ x : X, x ≠ 1 ∧ x ^ 3 = 1 := by
  have h : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 ∧ Multiplicative.ofAdd (1 : ZMod 3) ^ 3 = 1 := by
    decide
  refine ⟨e.symm (Multiplicative.ofAdd 1), fun h1 => h.1 ?_, ?_⟩
  · have := congrArg e h1
    simp at this
  · rw [← map_pow, h.2, map_one]

theorem exists_ne_one_pow_three_of_perm3 (e : X ≃* Equiv.Perm (Fin 3)) :
    ∃ x : X, x ≠ 1 ∧ x ^ 3 = 1 := by
  have h : finRotate 3 ≠ 1 ∧ finRotate 3 ^ 3 = 1 := by decide
  refine ⟨e.symm (finRotate 3), fun h1 => h.1 ?_, ?_⟩
  · have := congrArg e h1
    simpa using this
  · rw [← map_pow, h.2, map_one]

end Orders

end CFSG.RankThree.PartTwo.Sec12.Proof128
