module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Background.B1Offender
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.EmptyFaithful.S141Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Abstract

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isElemAbelian2_zpowers_of_sq {s : MulAut V} (hs : s ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs

omit [Finite V] in
theorem dualGrp_sq (f : DualGrp V) : f ^ 2 = 1 := by
  refine DualGrp.ext fun v => ?_
  have h : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide
  rw [pow_two]
  exact h (f v)

theorem not_isFFModule_dualSub_of_one_lt_qOf (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hq : ¬ qOf X ≤ 1) : ¬ IsFFModule (dualSub X) := by
  intro hff
  have hWsq : ∀ f : DualGrp V, f ^ 2 = 1 := dualGrp_sq
  obtain ⟨A, hA, hr⟩ := (isFFModule_iff hWsq).1 hff
  obtain ⟨B, -, hB, -⟩ := B1_4_4_le hWsq hA hr
  obtain ⟨A₀, -, hmin⟩ := B1.exists_isFFStarMin_le hB
  have hinj : Function.Injective (dualAct V) := dualAct_injective hV
  have hsolvX : Group.IsSolvable ↥(dualSub X) := by
    have := hsolv
    exact Group.isSolvable_of_surjective
      (f := (X.equivMapOfInjective (dualAct V) hinj).toMonoidHom)
      (X.equivMapOfInjective (dualAct V) hinj).surjective
  have hO2X : ∀ Q : Subgroup (MulAut (DualGrp V)), Q ≤ dualSub X →
      (Q.subgroupOf (dualSub X)).Normal → IsPGroup 2 Q → Q = ⊥ := by
    intro Q hQX hQn hQ2
    have hnorm : ∀ g ∈ dualSub X, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := by
      intro g hg y hy
      have := hQn.conj_mem ⟨y, hQX hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
      exact Subgroup.mem_subgroupOf.mp this
    have hQ' := hO2 (Q.comap (dualAct V) ⊓ X) inf_le_right ?_ ?_
    · rw [eq_bot_iff]
      intro q hq'
      obtain ⟨a, haX, rfl⟩ := hQX hq'
      have : a ∈ Q.comap (dualAct V) ⊓ X := ⟨hq', haX⟩
      rw [hQ', Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnQ, hnX⟩ := hn
      have hcoe : ((g * n * g⁻¹ : ↥X) : MulAut V) =
          (g : MulAut V) * (n : MulAut V) * (g : MulAut V)⁻¹ := rfl
      rw [hcoe]
      refine ⟨?_, X.mul_mem (X.mul_mem g.2 hnX) (X.inv_mem g.2)⟩
      show dualAct V ((g : MulAut V) * n * (g : MulAut V)⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ ⟨g, g.2, rfl⟩ _ hnQ
    · intro y
      obtain ⟨k, hk⟩ := hQ2 ⟨dualAct V y, y.2.1⟩
      refine ⟨k, Subtype.ext (hinj ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
  obtain ⟨t, htX, htt, hAt⟩ := B1.exists_transvection_of_isFFStarMin hWsq hsolvX hO2X hmin
  obtain ⟨s, hsX, rfl⟩ := htX
  obtain ⟨ht1, w, htw⟩ := htt
  have hs1 : s ≠ 1 := fun h => ht1 (by rw [h]; exact map_one _)
  have hs2 : s ^ 2 = 1 := by
    apply hinj
    have h2 := B1.tv_sq hWsq htw ht1
    rw [map_pow, map_one, pow_two]
    exact h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hcardA : Nat.card (Subgroup.zpowers s) = 2 := by rw [Nat.card_zpowers, hord]
  have hrkA : rk ↥(Subgroup.zpowers s) = 1 := by
    unfold rk
    rw [hcardA, padicValNat_self]
  have hdual : dualSub (Subgroup.zpowers s) = Subgroup.zpowers (dualAct V s) := by
    unfold dualSub
    rw [MonoidHom.map_zpowers]
  have hcomm2 : Nat.card (commV (Subgroup.zpowers s)) = 2 := by
    have h1 := index_fixV_dualSub hV (Subgroup.zpowers s)
    rw [hdual] at h1
    have h2 := B1.card_eq_two_mul_fixV_of_tv hWsq ht1 htw
    have h3 := Subgroup.card_mul_index (fixV (Subgroup.zpowers (dualAct V s)))
    have hpos : 0 < Nat.card (fixV (Subgroup.zpowers (dualAct V s))) := Nat.card_pos
    rw [← h1]
    rw [h2] at h3
    have : (fixV (Subgroup.zpowers (dualAct V s))).index = 2 := by
      have h4 : Nat.card (fixV (Subgroup.zpowers (dualAct V s))) * 2 =
          Nat.card (fixV (Subgroup.zpowers (dualAct V s))) *
            (fixV (Subgroup.zpowers (dualAct V s))).index := by
        rw [mul_comm]
        exact h3.symm
      exact (Nat.eq_of_mul_eq_mul_left hpos h4).symm
    exact this
  have hrkc : rk ↥(commV (Subgroup.zpowers s)) = 1 := by
    unfold rk
    rw [hcomm2, padicValNat_self]
  have hr : rAV (Subgroup.zpowers s) ≤ 1 := by
    unfold rAV
    rw [rkIdx_fixV_zpowers, hrkc, hrkA]
    norm_num
  have hA2 : IsA2 X (Subgroup.zpowers s) :=
    ⟨Subgroup.zpowers_le.mpr hsX, fun h => hs1 (by simpa using
      (Subgroup.zpowers_eq_bot.mp h)), isElemAbelian2_zpowers_of_sq hs2⟩
  apply hq
  have := qOf_le_iff.mpr ⟨Subgroup.zpowers s, hA2, isQuadratic_zpowers hV hs2, hr⟩
  simpa using this

end Abstract

section Internal

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_autOn_of_perfectCore_le {M V : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (h : perfectCore M ≤ Subgroup.centralizer (V : Set G)) : Group.IsSolvable ↥(autOn M V) := by
  rw [isSolvable_iff_perfectCore_eq_bot, eq_bot_iff]
  have h1 : perfectCore (autOn M V) =
      (perfectCore (M.subgroupOf (Subgroup.normalizer (V : Set G)))).map (conjAct V) := by
    unfold autOn
    exact (map_perfectCore _ _).symm
  rw [h1]
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  have hxM : (x : G) ∈ perfectCore M := by
    have h2 := map_perfectCore (Subgroup.normalizer (V : Set G)).subtype
      (M.subgroupOf (Subgroup.normalizer (V : Set G)))
    rw [Subgroup.map_subgroupOf_eq_of_le hMV] at h2
    rw [← h2]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact Subgroup.mem_bot.mpr (A4.conjAct_eq_one_iff.mpr (h hxM))

omit [Finite G] in
theorem autOn_pCore_trivial {M V : Subgroup G} (hred : IsTwoReducedIn M V) :
    ∀ Q : Subgroup (MulAut V), Q ≤ autOn M V → (Q.subgroupOf (autOn M V)).Normal →
      IsPGroup 2 Q → Q = ⊥ := by
  intro Q hQ hQn hQ2
  have hMV := hred.2.1
  have hL : ∀ g ∈ autOn M V, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := by
    intro g hg y hy
    have := hQn.conj_mem ⟨y, hQ hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hDM : preOn M V Q ≤ M := preOn_le _ _ _
  have hMD : M ≤ Subgroup.normalizer (preOn M V Q : Set G) := le_normalizer_preOn hMV hL
  have hpow : ∀ d ∈ preOn M V Q, ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨hdM, hdN, hdQ⟩ := mem_preOn.mp hd
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hdQ⟩
    have hyN : d ^ 2 ^ k ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hdN _
    refine ⟨k, (A4.conjAct_eq_one_iff (g := ⟨d ^ 2 ^ k, hyN⟩)).mp ?_⟩
    have hk' : (conjAct V ⟨d, hdN⟩) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← hk', ← map_pow]
    rfl
  have hDC := hred.2.2.2 _ hDM hMD hpow
  have hQeq : autOn (preOn M V Q) V = Q := autOn_preOn hQ
  rw [← hQeq, eq_bot_iff]
  intro a ha
  obtain ⟨x, hxN, hxD, rfl⟩ := mem_autOn_iff_exists.mp ha
  exact Subgroup.mem_bot.mpr (A4.conjAct_eq_one_iff.mpr (hDC hxD))

theorem not_isDualFFInt_of_one_lt_qInt {M₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hsolv : Group.IsSolvable ↥(autOn M₀ V))
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ autOn M₀ V →
      (Q.subgroupOf (autOn M₀ V)).Normal → IsPGroup 2 Q → Q = ⊥)
    (hq : ¬ qInt M₀ V hV ≤ 1) : ¬ IsDualFFInt M₀ V hV := by
  let _inst : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  exact not_isFFModule_dualSub_of_one_lt_qOf hV2 hsolv hO2 hq

theorem qOn_eq_two_of_lemma1518 {T Mc M : Subgroup G} (h : Lemma1518Concl T Mc M) :
    qOn M (V154 T Mc M) = 2 := by
  rcases h with h' | h'
  · exact h'.2
  · exact h'.2.2

theorem notDualFF1512_of (h1416 : StageLemma1416) (h1515 : StageLemma1515)
    (h158 : StageLemma1518) (h159 : StageLemma1519) : NotDualFF1512 := by
  intro G _ _ T Mc M h hM hCE
  have hred : IsTwoReducedIn M (V154 T Mc M) := (h1515 G T Mc M h hM).reduced
  have hsix : autOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M) =
      autOn M (V154 T Mc M) := (h159 G T Mc M h hM hCE).six_autOn
  have hsolv : Group.IsSolvable ↥(autOn M (V154 T Mc M)) :=
    isSolvable_autOn_of_perfectCore_le hred.2.1 ((h1416 G T Mc h).1 M _ hM.1.1 hred)
  rintro ⟨hV, hd⟩
  refine not_isDualFFInt_of_one_lt_qInt hV (by rw [hsix]; exact hsolv)
    (by rw [hsix]; exact autOn_pCore_trivial hred) ?_ hd
  have hq2 : qInt M (V154 T Mc M) hV = 2 := by
    rw [← qOn_eq hV]
    exact qOn_eq_two_of_lemma1518 (h158 G T Mc M h hM hCE)
  rw [qInt_congr hV hsix, hq2]
  norm_num

end Internal

end CFSG.Quasithin
