module

public import CFSG.LocalAnalysis.QuasithinUnique.Theorem211Proved
public import CFSG.Quasithin.Background.RonanE628RTorus
public import CFSG.ClassicalInvolution.Q3.M11Multiplier
public import CFSG.ClassicalInvolution.Uniform.UMember

public section

namespace CFSG.Quasithin.RonanE628.MathAS4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6
open CFSG.ComponentClassification.AschbacherToolkit (Bender.sylowCenter_le Bender.mem_sylowCenter
  Bender.normalizer_transitive_center Bender.benderBorel_sylowCenter BenderExt.benderData_of_isBenderGroup)
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Thm211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    fusionIsBenderGroup G ∨ UniqueSmallModel G

theorem uniqueSetting_of_hypE61 {T M V : Subgroup G} (h : HypE61 T M V) (hu : IsUniqueM T M) :
    UniqueSetting G T M := by
  haveI := h.simple
  exact ⟨h.simple, h.nonabelian, qtkeCore_of_cat h.nonabelian h.qtke,
    ⟨le_top, h.sylow.1, fun hd => h.sylow.2 (by
      rw [← Subgroup.relIndex_top_right]; exact hd)⟩,
    hu.1.1, hu.1.2, fun M' hM' hTM' => hu.2 M' ⟨hM', hTM'⟩⟩

@[expose] def ConjCrit (X : Type*) [Group X] : Prop :=
  ∃ z : X, ∀ t : X, t ^ 2 = 1 → t ≠ 1 → t ≠ z → ∃ s : X, (t * (s * t * s⁻¹)) ^ 2 ≠ 1

theorem ConjCrit.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : ConjCrit Y) :
    ConjCrit X := by
  obtain ⟨z, hz⟩ := h
  refine ⟨e.symm z, fun t ht2 ht1 htz => ?_⟩
  obtain ⟨s, hs⟩ := hz (e t) (by rw [← map_pow, ht2, map_one])
    (by rwa [Ne, map_eq_one_iff e e.injective]) (fun h => htz (by rw [← h, e.symm_apply_apply]))
  refine ⟨e.symm s, fun h => hs ?_⟩
  have := congrArg e h
  simpa using this

theorem mem_pair_of_conjCrit {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hN : T ≤ Subgroup.normalizer (V : Set G)) {z : ↥T}
    (hz : ∀ t : ↥T, t ^ 2 = 1 → t ≠ 1 → t ≠ z → ∃ s : ↥T, (t * (s * t * s⁻¹)) ^ 2 ≠ 1)
    {v : G} (hv : v ∈ V) : v = 1 ∨ v = z := by
  by_contra hne
  push Not at hne
  obtain ⟨s, hs⟩ := hz ⟨v, hVT hv⟩ (Subtype.ext (by simpa using hV.2 v hv))
    (fun h => hne.1 (congrArg Subtype.val h)) (fun h => hne.2 (congrArg Subtype.val h))
  have hsv : (s : G) * v * (s : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hN s.2) v).mp hv
  exact hs (Subtype.ext (by simpa using hV.2 _ (V.mul_mem hv hsv)))

theorem rParam_le_one_of_conjCrit {T M V : Subgroup G} (h : HypE61 T M V) (hc : ConjCrit ↥T) :
    E3.rParam V ≤ 1 := by
  obtain ⟨z, hz⟩ := hc
  have hsub : (V : Set G) ⊆ ({1, (z : G)} : Set G) := fun v hv =>
    mem_pair_of_conjCrit h.isElemAbelian h.le h.normal hz hv
  have hcard : Nat.card V ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  have hpos : 0 < Nat.card V := Nat.card_pos
  have hle := rParam_le_mQuot_bot h
  have hm : E3.mQuot V ⊥ ≤ 1 := by
    rw [E3.mQuot, Subgroup.relIndex_bot_left]
    interval_cases hc : Nat.card V <;> simp
  exact hle.trans (by exact_mod_cast hm)

theorem conjCrit_dihedral {n : ℕ} (hn0 : 0 < n) (hn : ¬ n ∣ 4) : ConjCrit (DihedralGroup n) := by
  haveI : NeZero n := ⟨hn0.ne'⟩
  refine ⟨DihedralGroup.r ((n / 2 : ℕ) : ZMod n), fun t ht2 ht1 htz => ?_⟩
  rcases t with i | i
  · exfalso
    rw [sq, DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at ht2
    have hdvd : n ∣ i.val + i.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val, ht2]
    have hlt := ZMod.val_lt i
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c < 2 := by
      by_contra hc2
      have : n * 2 ≤ n * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c
    · rw [mul_zero] at hc
      apply ht1
      rw [DihedralGroup.one_def, DihedralGroup.r.injEq, ← ZMod.natCast_zmod_val i]
      have : i.val = 0 := by omega
      rw [this, Nat.cast_zero]
    · rw [mul_one] at hc
      apply htz
      rw [DihedralGroup.r.injEq, ← ZMod.natCast_zmod_val i]
      congr 1
      omega
  · refine ⟨DihedralGroup.r 1, fun h => hn ?_⟩
    simp only [sq, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r, DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at h
    have h4 : ((4 : ℕ) : ZMod n) = 0 := by
      have : ((4 : ℕ) : ZMod n) = -(i - 1 + -1 - i + (i - 1 + -1 - i)) := by push_cast; ring
      rw [this, h, neg_zero]
    exact (ZMod.natCast_eq_zero_iff 4 n).mp h4

theorem conjCrit_sylow (P Q : Sylow 2 G) (h : ConjCrit ↥(P : Subgroup G)) :
    ConjCrit ↥(Q : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (Q : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  exact h.of_mulEquiv ((MulEquiv.subgroupCongr hQ).trans
    (Subgroup.equivSMul (MulAut.conj g) (P : Subgroup G)).symm)

theorem conjCrit_sylow_of_mulEquiv {H : Type*} [Group H] [Finite H] (e : G ≃* H) (Q : Sylow 2 H)
    (hQ : ConjCrit ↥(Q : Subgroup H)) (T : Sylow 2 G) : ConjCrit ↥(T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Q.comapOfInjective e.toMonoidHom e.injective (by
    rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  have hP : ((P : Subgroup G).map e.toMonoidHom) = Q := by
    change ((Q : Subgroup H).comap e.toMonoidHom).map e.toMonoidHom = Q
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  exact conjCrit_sylow P T (hQ.of_mulEquiv ((e.subgroupMap (P : Subgroup G)).trans
    (MulEquiv.subgroupCongr hP)))

theorem four_le_factorization_psl2 {p : ℕ} (hp7 : 7 < p)
    (hpF : (∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1)) :
    4 ≤ (p * (p ^ 2 - 1) / 2).factorization 2 := by
  rcases hpF with ⟨k, rfl⟩ | ⟨k, hk, rfl⟩
  · have hk2 : 2 ≤ k := by
      by_contra hk
      interval_cases k <;> norm_num at hp7
    have ha : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ k = b + 1 := ⟨2 ^ k - 1, by omega⟩
    have hhalf : (2 ^ 2 ^ k + 1 - 1) / 2 = 2 ^ b := by
      rw [hb, pow_succ]; omega
    have hodd : Odd (2 ^ 2 ^ k + 1) := by
      rw [hb, pow_succ]; exact ⟨2 ^ b, by ring⟩
    rw [GorensteinWalter.psl2_order_two_factorization_split hodd (by omega)
      (by rw [hhalf]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩), hhalf,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.single_eq_same]
    omega
  · have hk4 : 4 ≤ k := by
      by_contra hk'
      interval_cases k <;> norm_num at hp7
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : 8 ≤ 2 ^ j := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hodd : Odd (2 ^ (j + 1) - 1) := by
      rw [pow_succ]; exact ⟨2 ^ j - 1, by omega⟩
    have hhalf1 : (2 ^ (j + 1) - 1 - 1) / 2 = 2 ^ j - 1 := by rw [pow_succ]; omega
    have hhalf2 : (2 ^ (j + 1) - 1 + 1) / 2 = 2 ^ j := by rw [pow_succ]; omega
    have hoj : Odd (2 ^ j - 1) := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by
        rcases j with _ | j
        · norm_num at hj
        · omega⟩
      rw [pow_succ]; exact ⟨2 ^ i - 1, by omega⟩
    rw [GorensteinWalter.psl2_order_two_factorization_nonsplit hodd (by omega)
      (by rw [hhalf1]; exact hoj), hhalf2, Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.single_eq_same]
    omega

theorem conjCrit_psl2 {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpF : (∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1)) :
    ∃ Q : Sylow 2 PSL(2, ZMod p), ConjCrit ↥(Q : Subgroup PSL(2, ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [Nat.card_zmod, pow_one]⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 PSL(2, ZMod p)) := inferInstance
  obtain ⟨m, -, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod p) hodd S
  have hcard : Nat.card S = 2 ^ (Nat.card PSL(2, ZMod p)).factorization 2 :=
    Sylow.card_eq_multiplicity S
  rw [show Nat.card PSL(2, ZMod p) = _ from GorensteinWalter.psl2_card_formula (ZMod p) hodd,
    Nat.card_zmod] at hcard
  have hD : Nat.card S = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have h16 : 16 ≤ 2 * 2 ^ m := by
    rw [← hD, hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (four_le_factorization_psl2 hp7 hpF)
  refine ⟨S, (conjCrit_dihedral (by positivity) fun hdvd => ?_).of_mulEquiv e⟩
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

section M11

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform Equiv

theorem m11Sd_crit : ∀ p : Fin 8 × Fin 2, m11SdMap p ^ 2 = 1 → m11SdMap p ≠ 1 →
    m11SdMap p ≠ m11SdX ^ 4 → ∃ q : Fin 8 × Fin 2,
      (m11SdMap p * (m11SdMap q * m11SdMap p * (m11SdMap q)⁻¹)) ^ 2 ≠ 1 := by
  decide +kernel

theorem conjCrit_m11SdS : ConjCrit ↥m11SdS := by
  have hxS : (⟨m11SdX, m11SdX_mem⟩ : ↥CFSG.Blueprint.NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  refine ⟨⟨_, pow_mem hxS 4⟩, fun t ht2 ht1 htz => ?_⟩
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem t.2
  obtain ⟨⟨t', htM⟩, htS⟩ := t
  simp only at hp
  subst hp
  have hval : ∀ u : ↥m11SdS, ((u : ↥CFSG.Blueprint.NativeSporadic.M11) : Perm (Fin 11)) = 1 →
      u = 1 := fun u hu => Subtype.ext (Subtype.ext hu)
  obtain ⟨q, hq⟩ := m11Sd_crit p (by simpa using congrArg (fun u : ↥m11SdS =>
      ((u : ↥CFSG.Blueprint.NativeSporadic.M11) : Perm (Fin 11))) ht2)
    (fun h => ht1 (hval _ h))
    (fun h => htz (Subtype.ext (Subtype.ext (by simpa using h))))
  have hyS : (⟨m11SdY, m11SdY_mem⟩ : ↥CFSG.Blueprint.NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨⟨_, mul_mem (pow_mem hxS q.1.val) (pow_mem hyS q.2.val)⟩, fun h => hq ?_⟩
  have := congrArg (fun u : ↥m11SdS => ((u : ↥CFSG.Blueprint.NativeSporadic.M11) : Perm (Fin 11))) h
  simpa [m11SdMap] using this

theorem conjCrit_sd16 : ConjCrit (CFSG.Open.SemidihedralGroup 4) := by
  have hxS : (⟨m11SdX, m11SdX_mem⟩ : ↥CFSG.Blueprint.NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hyS : (⟨m11SdY, m11SdY_mem⟩ : ↥CFSG.Blueprint.NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Unc25Small.nonempty_mulEquiv_semidihedral
    (H := ↥m11SdS) ⟨_, hxS⟩ ⟨_, hyS⟩
    (Subtype.ext (Subtype.ext (by simpa using m11SdX_pow_eight)))
    (Subtype.ext (Subtype.ext (by simpa using m11SdY_sq)))
    (Subtype.ext (Subtype.ext (by simpa using m11SdY_conj)))
    (fun u => by
      obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem u.2
      exact ⟨p.1.val, p.2.val, Subtype.ext (Subtype.ext (by simpa [m11SdMap] using hp.symm))⟩)
    (by rw [card_m11SdS])
  exact conjCrit_m11SdS.of_mulEquiv e.symm

theorem m11SdS_card_eq_sylow :
    Nat.card m11SdS = 2 ^ (Nat.card ↥CFSG.Blueprint.NativeSporadic.M11).factorization 2 := by
  rw [card_m11SdS, card_m11_kernel]
  have h2 : (7920 : ℕ).factorization 2 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h : (7920 : ℕ) = 2 ^ 4 * 495 := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have : padicValNat 2 495 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  rw [h2]; norm_num

theorem conjCrit_m11 : ∃ Q : Sylow 2 ↥M11, ConjCrit ↥(Q : Subgroup ↥M11) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* ↥M11 :=
    (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11).symm.trans
      CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11
  haveI : Finite ↥M11 := Finite.of_equiv _ e.toEquiv
  let P₀ : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M11 := Sylow.ofCard m11SdS m11SdS_card_eq_sylow
  have hP₀ : ConjCrit ↥(P₀ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11) := conjCrit_m11SdS
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥M11) := inferInstance
  exact ⟨Q, conjCrit_sylow_of_mulEquiv e.symm P₀ hP₀ Q⟩

end M11

theorem center_sl33_eq_bot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have key : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide
    obtain rfl := key r (by simpa using hr)
    exact Subtype.ext (hA.symm.trans (by simp))
  · rintro rfl
    exact ⟨1, one_pow _, by ext; simp⟩

theorem conjCrit_psl33 :
    ∃ Q : Sylow 2 PSL(3, ZMod 3), ConjCrit ↥(Q : Subgroup PSL(3, ZMod 3)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : PSL(3, ZMod 3) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
    (QuotientGroup.quotientMulEquivOfEq center_sl33_eq_bot).trans QuotientGroup.quotientBot
  obtain ⟨-, hP2, hPi⟩ := CFSG.QuasithinUnique.Unc25L33.isSylowTwoOf_P0
  let P₀ : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :=
    IsPGroup.toSylow hP2 (fun hd => hPi (by rwa [← Subgroup.relIndex_top_right] at hd))
  obtain ⟨f⟩ := CFSG.QuasithinUnique.Unc25L33.shape_P0
  have hP₀ : ConjCrit ↥(P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))) :=
    conjCrit_sd16.of_mulEquiv (MulEquiv.subgroupCongr (IsPGroup.toSylow_coe _ _) |>.trans f)
  obtain ⟨Q⟩ : Nonempty (Sylow 2 PSL(3, ZMod 3)) := inferInstance
  exact ⟨Q, conjCrit_sylow_of_mulEquiv e P₀ hP₀ Q⟩

theorem not_uniqueSmallModel
    {T M V : Subgroup G} (h : HypE61 T M V) (hr : 1 < E3.rParam V) :
    ¬ UniqueSmallModel G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := IsPGroup.toSylow h.sylow.1 h.sylow.2
  have hS : (S : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have key : ConjCrit ↥T → False := fun hc =>
    absurd (rParam_le_one_of_conjCrit h hc) (not_le.mpr hr)
  rintro (⟨p, hp, hp7, hpF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)
  · haveI : Finite PSL(2, ZMod p) := Finite.of_equiv G e.toEquiv
    obtain ⟨Q, hQ⟩ := conjCrit_psl2 hp hp7 hpF
    exact key (hS ▸ conjCrit_sylow_of_mulEquiv e Q hQ S)
  · haveI : Finite PSL(3, ZMod 3) := Finite.of_equiv G e.toEquiv
    obtain ⟨Q, hQ⟩ := conjCrit_psl33
    exact key (hS ▸ conjCrit_sylow_of_mulEquiv e Q hQ S)
  · haveI : Finite ↥M11 := Finite.of_equiv G e.toEquiv
    obtain ⟨Q, hQ⟩ := conjCrit_m11
    exact key (hS ▸ conjCrit_sylow_of_mulEquiv e Q hQ S)

theorem normalizer_le_of_isUniqueM {T M : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hu : IsUniqueM T M) : Subgroup.normalizer (T : Set G) ≤ M := by
  obtain ⟨M', hM', hle⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge (G := G)
    (L := Subgroup.normalizer (T : Set G)) ⟨T, hT1, hT, rfl⟩
  have hTM' : T ≤ M' := Subgroup.le_normalizer.trans hle
  rw [← hu.2 M' ⟨hM', hTM'⟩]
  exact hle

theorem borelTorus_of_bender {T M V : Subgroup G}
    (h : HypE61 T M V) (hu : IsUniqueM T M) (hB : fusionIsBenderGroup G) :
    ∃ P K : Subgroup G, IsElemAbelian 2 P ∧ P ≤ T ∧
      (∀ t ∈ T, t * t = 1 → t ∈ P) ∧ K ≤ M ∧ IsCyclic K ∧ Odd (Nat.card K) ∧
      K ≤ Subgroup.normalizer (T : Set G) ∧ K ≤ Subgroup.normalizer (P : Set G) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ 1 → q ≠ 1 → ∃ k ∈ K, k⁻¹ * p * k = q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := IsPGroup.toSylow h.sylow.1 h.sylow.2
  have hS : (S : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  obtain ⟨q, k, -, hBB⟩ := (BenderExt.benderData_of_isBenderGroup hB).borel
  obtain ⟨hSE, ⟨D, hDc, hDodd, -, hTD⟩, -, -, -⟩ := hBB S
  rw [hS] at hSE hTD
  obtain ⟨-, hZ2, -, -⟩ := Bender.benderBorel_sylowCenter hBB S
  rw [hS] at hZ2
  have hΩ : CFSG.Goldschmidt.Omega1 T = sylowCenter T := by
    have := CFSG.Goldschmidt.GoldType.omega1_eq_sylowCenter_of_bender hB S
    rwa [hS] at this
  have hT1 : T ≠ ⊥ := fun hT => h.ne_bot (eq_bot_iff.mpr (hT ▸ h.le))
  have hNM := normalizer_le_of_isUniqueM h.sylow.1 hT1 hu
  have hDN : D ≤ Subgroup.normalizer (T : Set G) := hTD ▸ le_sup_right
  have hNP : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (sylowCenter T : Set G) := by
    rw [← hΩ]; exact CFSG.Goldschmidt.GoldType.normalizer_le_normalizer_omega1 T
  refine ⟨sylowCenter T, D, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hZ2 x hx⟩,
    Bender.sylowCenter_le T, fun t ht htt => ?_, hDN.trans hNM, hDc, hDodd, hDN, hDN.trans hNP,
    fun p hp q hq hp1 hq1 => ?_⟩
  · exact ((Bender.mem_sylowCenter.mp b.2).2 a (Bender.sylowCenter_le T a.2))
  · rw [← hΩ]; exact CFSG.Goldschmidt.GoldType.mem_omega1 ht (by rw [sq]; exact htt)
  · obtain ⟨n, hn, hnpq⟩ := Bender.normalizer_transitive_center hSE hZ2 hp hq hp1 hq1
    have hn' : n ∈ ((T ⊔ D : Subgroup G) : Set G) := by rw [hTD]; exact hn
    rw [Subgroup.coe_mul_of_right_le_normalizer_left T D (hTD ▸ le_sup_right)] at hn'
    obtain ⟨t, ht, d, hd, rfl⟩ := hn'
    refine ⟨d, hd, ?_⟩
    have htp : t * p = p * t := (Bender.mem_sylowCenter.mp hp).2 t ht
    rw [← hnpq]
    calc d⁻¹ * p * d = d⁻¹ * (t⁻¹ * (t * p)) * d := by group
      _ = (t * d)⁻¹ * p * (t * d) := by rw [htp]; group

theorem uniqueMBorelTorusR_of_thm211
    (h211 : Thm211) : UniqueMBorelTorusR := by
  intro G _ _ T M V h hr hu
  rcases h211 G T M (uniqueSetting_of_hypE61 h hu) with hB | hS
  · exact borelTorus_of_bender h hu hB
  · exact (not_uniqueSmallModel h hr hS).elim

theorem uniqueMBorelTorusR_holds :
    UniqueMBorelTorusR :=
  uniqueMBorelTorusR_of_thm211 theorem_2_1_1_proved

end CFSG.Quasithin.RonanE628.MathAS4
