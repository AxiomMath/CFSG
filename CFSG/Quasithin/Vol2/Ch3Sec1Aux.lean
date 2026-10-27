module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542FourModule
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section KqSylow

variable {V : Type*} [CommGroup V]

theorem conjBy_eq_conjSub_of_aut (g : MulAut V) (Y : Subgroup (MulAut V)) :
    conjBy g Y = B6.conjSub g Y := by
  ext x
  rw [mem_conjBy_iff, B6.mem_conjSub]

theorem exists_conjBy_le_of_isSylowTwoOf [Finite V] {X Y A : Subgroup (MulAut V)}
    (hY : IsSylowTwoOf Y X) (hAX : A ≤ X) (hA : IsPGroup 2 A) : ∃ g ∈ X, conjBy g A ≤ Y := by
  obtain ⟨S, hS, hAS⟩ := B6.exists_isSylowTwoOf_ge hA hAX
  obtain ⟨g, hg, hYS⟩ := B6.isSylowTwoOf_exists_conj hS hY
  refine ⟨g, hg, ?_⟩
  intro x hx
  rw [mem_conjBy_iff] at hx
  rw [hYS, B6.mem_conjSub]
  exact hAS hx

variable [Finite V]

theorem kq_anti_group {X Y : Subgroup (MulAut V)} (h : X ≤ Y) (k : ℕ) : kq Y k ≤ kq X k :=
  CFSG.Quasithin.EmptyFaithfulMultiple.kq_le_kq_of_le h k

theorem kq_le_of_isSylowTwoOf {X Y Z : Subgroup (MulAut V)} (hY : IsSylowTwoOf Y X)
    (hYZ : Y ≤ Z) (k : ℕ) : kq Z k ≤ kq X k := by
  rcases h : kq X k with _ | r
  · exact le_top
  · have hr : kq X k ≤ (r : WithTop ℚ) := by rw [h]; exact le_rfl
    obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp hr
    have hA2 : IsPGroup 2 A := hA.isElemAbelian2.isPGroup
    obtain ⟨g, hgX, hgA⟩ := exists_conjBy_le_of_isSylowTwoOf hY hA.le hA2
    have hA' : IsA2 X (conjBy g A) := hA.conjBy hgX
    have hA'Z : IsA2 Z (conjBy g A) := ⟨hgA.trans hYZ, hA'.ne_bot, hA'.isElemAbelian2⟩
    refine kq_le_iff.mpr ⟨conjBy g A, hA'Z, ?_, ?_⟩
    · exact (commSeries_conjBy_eq_bot_iff g A k).mpr hAk
    · rw [rAV_conjBy]; exact hAr

end KqSylow

section QTransfer

variable {G : Type} [Group G]

omit [Group G] in
theorem autOn_eq_autOn_inf [Group G] (H V : Subgroup G) :
    autOn H V = autOn (H ⊓ Subgroup.normalizer (V : Set G)) V := by
  unfold autOn
  congr 1
  ext x
  simp [Subgroup.mem_subgroupOf]

variable [Finite G]

theorem kq_autOn_le_of_isSylowTwoOf {T H M₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTH : IsSylowTwoOf T H) (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTM₀ : T ≤ M₀)
    (k : ℕ) :
    @kq ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M₀ V) k ≤
      @kq ↥V (commGroupOfElemAbelian hV) inferInstance (autOn H V) k := by
  have hTK : IsSylowTwoOf T (H ⊓ Subgroup.normalizer (V : Set G)) :=
    B6.isSylowTwoOf_mono hTH (le_inf hTH.1 hTV) inf_le_left
  have hS := B2F.isSylowTwoOf_autI hV
    (inf_le_right : H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (V : Set G)) hTK
  rw [autOn_eq_autOn_inf H V]
  exact kq_le_of_isSylowTwoOf (V := IntMod V hV) hS (autI_mono hV hTM₀) k

theorem qhatInt_le_of_isSylowTwoOf {T H M₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTH : IsSylowTwoOf T H) (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTM₀ : T ≤ M₀) :
    qhatInt M₀ V hV ≤ qhatInt H V hV :=
  kq_autOn_le_of_isSylowTwoOf hV hTH hTV hTM₀ 3

theorem qhatInt_le_qInt (M₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    qhatInt M₀ V hV ≤ qInt M₀ V hV :=
  @qhatOf_le_qOf ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M₀ V)

end QTransfer

section Thompson

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_orderOf_two_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ x ∈ T, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥T) 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

omit [Finite G] in
theorem isElemAbelian_zpowers_of_orderOf_eq_two {y : G} (hy : orderOf y = 2) :
    IsElemAbelian 2 (Subgroup.zpowers y) ∧ Nat.card (Subgroup.zpowers y) = 2 := by
  refine ⟨⟨inferInstance, fun x hx => ?_⟩, by rw [Nat.card_zpowers, hy]⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hy2]

theorem one_le_pRank_two {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    1 ≤ CFSG.Open.pRank 2 T := by
  obtain ⟨y, hyT, hy⟩ := exists_mem_orderOf_two_of_isPGroup hT hne
  obtain ⟨h1, h2⟩ := isElemAbelian_zpowers_of_orderOf_eq_two hy
  exact le_pRank Nat.prime_two (Subgroup.zpowers_le.mpr hyT) h1 (k := 1) (by simp [h2])

theorem thompsonJ_ne_bot_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    thompsonJ T ≠ ⊥ := by
  obtain ⟨y, hyT, hy⟩ := exists_mem_orderOf_two_of_isPGroup hT hne
  obtain ⟨h1, h2⟩ := isElemAbelian_zpowers_of_orderOf_eq_two hy
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hle : Nat.card (Subgroup.zpowers y) ≤ Nat.card A :=
    hA.2.2 _ (Subgroup.zpowers_le.mpr hyT) h1
  intro hJ
  have hAbot : A = ⊥ := le_bot_iff.mp (hJ ▸ B6.le_thompsonJ hA)
  rw [hAbot, Subgroup.card_bot, h2] at hle
  omega

end Thompson

section AutOnTwoReduced

variable {G : Type*} [Group G] [Finite G]

theorem pCoreOf_autOn_eq_bot_of_isTwoReducedIn {M V : Subgroup G} (hred : IsTwoReducedIn M V) :
    pCoreOf 2 (autOn M V) = ⊥ := by
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  obtain ⟨D, hDM, hMD, hD2, -, hDQ⟩ := A4.exists_preimage_section hMV
    (Q := pCoreOf 2 (autOn M V)) (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _)
    (pCoreOf_isPGroup 2 _)
  have hDC : D ≤ Subgroup.centralizer (V : Set G) :=
    hred.2.2.2 D hDM hMD (fun d hd => by
      obtain ⟨k, hk⟩ := hD2 d hd
      exact ⟨k, hk.2⟩)
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, hxD, hxq⟩ := hDQ q hq
  have h1 : A4.actionOn V M hMV x = 1 := (A4.actionOn_eq_one_iff hMV x).mpr (hDC hxD)
  rw [Subgroup.mem_bot, ← hxq, h1]

end AutOnTwoReduced

end CFSG.Quasithin
