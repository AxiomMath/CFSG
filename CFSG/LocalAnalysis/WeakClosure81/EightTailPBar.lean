module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelOmega
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

structure TailSetup (V H T : Subgroup G) {X : Type} [Group X] (φ : ↥(kGenIn V H) →* X) : Prop where
  hyp83 : Hyp83 V H T
  eq_sup : H = kGenIn V H ⊔ T
  bar : IsBarMap (kGenIn V H) (Subgroup.centralizer (eSub V H T : Set G)) φ

theorem conjSubgroup_le_kGenIn_of_mem_H (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {a : G}
    (ha : a ∈ H) : conjSubgroup V a ≤ kGenIn V H := by
  intro x hx
  have hxV : a * x * a⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
  have hmem : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ ∈ conjClosure V H :=
    mem_conjClosure (H.inv_mem ha) hxV
  have he : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x := by group
  rw [he] at hmem
  rwa [h.conjClosure_eq_kGenIn hKT] at hmem

theorem exists_barMap_eCent (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    ∃ (X : Type) (_ : Group X) (φ : ↥(kGenIn V H) →* X),
      IsBarMap (kGenIn V H) (Subgroup.centralizer (eSub V H T : Set G)) φ := by
  let N := (Subgroup.centralizer (eSub V H T : Set G)).subgroupOf (kGenIn V H)
  have hN : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnC : ((n : ↥(kGenIn V H)) : G) ∈ Subgroup.centralizer (eSub V H T : Set G) := hn
    have hkK : (k : G) ∈ kGenIn V H := k.2
    have hkH : (k : G) ∈ H := (kGenIn_le_H h.le_H) hkK
    show ((k * n * k⁻¹ : ↥(kGenIn V H)) : G) ∈ Subgroup.centralizer (eSub V H T : Set G)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h.conj_mem_centralizer_eSub hkH hnC
  exact ⟨↥(kGenIn V H) ⧸ N, inferInstance, QuotientGroup.mk' N,
    QuotientGroup.mk'_surjective N, fun k => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl⟩

theorem not_conjSubgroup_le_centralizer_eSub (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {a : G}
    (ha : a ∈ H) : ¬ conjSubgroup V a ≤ Subgroup.centralizer (eSub V H T : Set G) := by
  intro hconj
  have hV : V ≤ Subgroup.centralizer (eSub V H T : Set G) := by
    intro x hx
    have heq : V = conjSubgroup (conjSubgroup V a) a⁻¹ := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hxW : x ∈ conjSubgroup (conjSubgroup V a) a⁻¹ := heq ▸ hx
    have hy : a⁻¹ * x * a ∈ conjSubgroup V a := by
      simpa using mem_conjSubgroup_iff.mp hxW
    have hyC : a⁻¹ * x * a ∈ Subgroup.centralizer (eSub V H T : Set G) := hconj hy
    have hxa := h.conj_mem_centralizer_eSub ha hyC
    simpa [mul_assoc] using hxa
  have hK : kGenIn V H ≤ Subgroup.centralizer (eSub V H T : Set G) := by
    refine iSup₂_le fun k hk => ?_
    intro x hx
    have hxV : k * x * k⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
    have hkH : k ∈ H := conjClosure_le_of_le_H h.le_H hk
    have hxV' : k * x * k⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G) := hV hxV
    have hxa := h.conj_mem_centralizer_eSub (H.inv_mem hkH) hxV'
    simpa [mul_assoc] using hxa
  have hKN : kGenIn V H ≤ Subgroup.normalizer (V : Set G) := by
    intro k hk
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.inf_eSub_ne_bot
    have hwV : (w : G) ∈ V := (Subgroup.mem_inf.mp w.2).1
    have hwE : (w : G) ∈ eSub V H T := (Subgroup.mem_inf.mp w.2).2
    have hw1 : (w : G) ≠ 1 := fun h' => hw (Subtype.ext h')
    have hkC : k ∈ Subgroup.centralizer (eSub V H T : Set G) := hK hk
    have hwN : k ∈ Subgroup.centralizer ({↑w} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_centralizer_iff.mp hkC (w : G) hwE
    have := centralizer_le_normalizer_conj h.isTI 1 (by rw [conjSubgroup_one]; exact hwV) hw1 hwN
    simpa [conjSubgroup_one] using this
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := by
    rw [hKT]
    exact sup_le hKN h.T_le_normalizer
  exact h.not_le_pCoreOf
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.le_H hHN
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian h.elemAbelian))

variable {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

theorem odd_card_center_bar (s : TailSetup V H T φ) : Odd (Nat.card (Subgroup.center X)) := by
  haveI : Finite X := Finite.of_surjective φ s.bar.surjective
  have hno : ∀ z ∈ Subgroup.center X, z * z = 1 → z = 1 := by
    intro z hz hzz
    obtain ⟨y, hy⟩ := s.bar.surjective z
    have hyPre : (y : G) ∈ centerPre (kGenIn V H) (eCentSet V H T) := by
      refine ⟨y.2, fun x hx => ?_⟩
      exact (s.bar.ker_iff (y * ⟨x, hx⟩ * y⁻¹ * ⟨x, hx⟩⁻¹)).mp (by
        simp only [map_mul, map_inv, hy]
        rw [← Subgroup.mem_center_iff.mp hz (φ ⟨x, hx⟩)]
        group)
    have hyy : ((y * y : ↥(kGenIn V H)) : G) ∈ eCentSet V H T :=
      (s.bar.ker_iff (y * y)).mp (by simp [map_mul, hy, hzz])
    have hyC : (y : G) ∈ eCentSet V H T :=
      mem_eCentSet_of_mem_centerPre s.hyp83 s.eq_sup hyPre hyy
    rw [← hy]
    exact (s.bar.ker_iff y).mpr hyC
  haveI : Fintype (Subgroup.center X) := Fintype.ofFinite _
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.card_eq_fintype_card] at hodd
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card 2 hodd
  have hz2' : orderOf (z : X) = 2 := (Subgroup.orderOf_coe z).trans hz2
  have hzz : (z : X) * (z : X) = 1 := by
    rw [← pow_two, ← hz2', pow_orderOf_eq_one]
  have hz1 : (z : X) = 1 := hno (z : X) z.2 hzz
  rw [hz1, orderOf_one] at hz2'
  omega

theorem conjSubgroup_eq_of_barSub_eq (s : TailSetup V H T φ) {a a' : G} (ha : a ∈ H)
    (ha' : a' ∈ H)
    (hbar : barSub (kGenIn V H) φ (conjSubgroup V a) = barSub (kGenIn V H) φ (conjSubgroup V a')) :
    conjSubgroup V a = conjSubgroup V a' := by
  classical
  have hnot := not_conjSubgroup_le_centralizer_eSub s.hyp83 s.eq_sup ha
  rw [SetLike.le_def] at hnot
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  obtain ⟨hxA, hxC⟩ := not_imp.mp hx
  have hxK : x ∈ kGenIn V H := conjSubgroup_le_kGenIn_of_mem_H s.hyp83 s.eq_sup ha hxA
  have hmem : φ ⟨x, hxK⟩ ∈ barSub (kGenIn V H) φ (conjSubgroup V a') := by
    rw [← hbar]
    exact mem_barSub.mpr ⟨⟨x, hxK⟩, hxA, rfl⟩
  obtain ⟨k, hkA', hkφ⟩ := mem_barSub.mp hmem
  have hφ1 : φ (⟨x, hxK⟩⁻¹ * k) = 1 := by
    simp only [map_mul, map_inv]
    rw [hkφ]
    group
  have hxx' : x⁻¹ * (k : G) ∈ eCentSet V H T := by
    simpa [eCentSet] using (s.bar.ker_iff (⟨x, hxK⟩⁻¹ * k)).mp hφ1
  exact conjSubgroup_eq_of_inv_mul_mem_eCentSet s.hyp83 s.eq_sup ha ha' hxA hxC hkA' hxx'

theorem exists_sylow_barSub_T (s : TailSetup V H T φ) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = barSub (kGenIn V H) φ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : kGenIn V H ≤ H := kGenIn_le_H s.hyp83.le_H
  have hKN : ((kGenIn V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (s.hyp83.le_normalizer_kGenIn_of_eq_sup s.eq_sup)
  have hSyl : IsSylowIn 2 (T ⊓ kGenIn V H) (kGenIn V H) :=
    s.hyp83.sylow_H.inf_normal hKH hKN
  let P₀ : Sylow 2 ↥(kGenIn V H) := hSyl.toSylow
  refine ⟨P₀.mapSurjective s.bar.surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  show ((T ⊓ kGenIn V H).subgroupOf (kGenIn V H)).map φ =
    (T.subgroupOf (kGenIn V H)).map φ
  rw [inf_subgroupOf_right]

private theorem w85g_barSub_cjSub_eq {K : Subgroup G} {Y : Type} [Group Y] {ψ : ↥K →* Y}
    {n : G} (hnK : n ∈ K) (hn1 : ψ ⟨n, hnK⟩ = 1) (A : Subgroup G) :
    barSub K ψ (cjSub n A) = barSub K ψ A := by
  apply le_antisymm
  · rintro y ⟨k, hk, rfl⟩
    have haA : n⁻¹ * (k : G) * n ∈ A := mem_cjSub.mp hk
    have haK : n⁻¹ * (k : G) * n ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hnK) k.2) hnK
    refine mem_barSub.mpr ⟨⟨n⁻¹ * (k : G) * n, haK⟩, haA, ?_⟩
    have he : (⟨n⁻¹ * (k : G) * n, haK⟩ : ↥K) = ⟨n, hnK⟩⁻¹ * k * ⟨n, hnK⟩ := by
      ext
      simp [mul_assoc]
    rw [he]
    simp only [map_mul, map_inv, hn1]
    group
  · rintro y ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hconjA : n * (a : G) * n⁻¹ ∈ cjSub n A := by
      rw [mem_cjSub]
      simpa [mul_assoc] using haA
    have hconjK : n * (a : G) * n⁻¹ ∈ K := K.mul_mem (K.mul_mem hnK a.2) (K.inv_mem hnK)
    refine mem_barSub.mpr ⟨⟨n * (a : G) * n⁻¹, hconjK⟩, hconjA, ?_⟩
    have he : (⟨n * (a : G) * n⁻¹, hconjK⟩ : ↥K) = ⟨n, hnK⟩ * a * ⟨n, hnK⟩⁻¹ := by
      ext
      simp [mul_assoc]
    rw [he]
    simp only [map_mul, map_inv, hn1]
    group

private theorem w85g_exists_mul_eq_of_mem_sup_of_le_normalizer {S N : Subgroup G}
    (hN : S ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ S ⊔ N) :
    ∃ s ∈ S, ∃ n ∈ N, s * n = x := by
  rw [sup_eq_closure] at hx
  refine closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, N.one_mem, by simp⟩
    · exact ⟨1, S.one_mem, x, hx, by simp⟩
  · exact ⟨1, S.one_mem, 1, N.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨s₁, hs₁, n₁, hn₁, rfl⟩ ⟨s₂, hs₂, n₂, hn₂, rfl⟩
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, (s₂⁻¹ * n₁ * s₂) * n₂,
      N.mul_mem (by simpa using (Subgroup.mem_normalizer_iff.mp (hN (S.inv_mem hs₂)) n₁).mp hn₁)
        hn₂, ?_⟩
    group
  · rintro _ _ ⟨s, hs, n, hn, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, s * n⁻¹ * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hN hs) n⁻¹).mp (N.inv_mem hn), ?_⟩
    group

private theorem w85g_barSub_conjSubgroup {K : Subgroup G} {Y : Type} [Group Y] {ψ : ↥K →* Y}
    (A : Subgroup G) (k : ↥K) :
    barSub K ψ (conjSubgroup A (k : G)) = conjSubgroup (barSub K ψ A) (ψ k) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_barSub.mp hy
    have haA : (k : G) * (x : G) * (k : G)⁻¹ ∈ A := mem_conjSubgroup_iff.mp hx
    have haK : (k : G) * (x : G) * (k : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem k.2 x.2) (K.inv_mem k.2)
    refine mem_conjSubgroup_iff.mpr ?_
    refine mem_barSub.mpr ⟨⟨(k : G) * (x : G) * (k : G)⁻¹, haK⟩, haA, ?_⟩
    have he : (⟨(k : G) * (x : G) * (k : G)⁻¹, haK⟩ : ↥K) = k * x * k⁻¹ := by
      ext
      simp
    rw [he]
    simp only [map_mul, map_inv]
  · intro hy
    rw [mem_conjSubgroup_iff] at hy
    obtain ⟨a, haA, hay⟩ := mem_barSub.mp hy
    have hxK : (k : G)⁻¹ * (a : G) * (k : G) ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem k.2) a.2) k.2
    have hxA : (k : G)⁻¹ * (a : G) * (k : G) ∈ conjSubgroup A (k : G) := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using haA
    refine mem_barSub.mpr ⟨⟨(k : G)⁻¹ * (a : G) * (k : G), hxK⟩, hxA, ?_⟩
    have he : (⟨(k : G)⁻¹ * (a : G) * (k : G), hxK⟩ : ↥K) = k⁻¹ * a * k := by
      ext
      simp
    rw [he]
    simp only [map_mul, map_inv]
    rw [hay]
    group

private theorem w85g_mk_comp_eq_one_iff_centerPre {K N : Subgroup G} {Y : Type} [Group Y]
    {φ : ↥K →* Y} (hφ : IsBarMap K N φ) (k : ↥K) :
    (QuotientGroup.mk' (Subgroup.center Y)) (φ k) = 1 ↔ (k : G) ∈ centerPre K N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  change (∀ g : Y, g * φ k = φ k * g) ↔
    (k : G) ∈ K ∧ ∀ x ∈ K, (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ N
  constructor
  · intro hk
    refine ⟨k.2, fun x hx => ?_⟩
    have h1 : φ (k * (⟨x, hx⟩ : ↥K) * k⁻¹ * (⟨x, hx⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hk (φ ⟨x, hx⟩)]
      group
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (hφ.ker_iff _).mp h1
  · rintro ⟨-, hx⟩ g
    obtain ⟨y, rfl⟩ := hφ.surjective g
    have h1 : φ (k * y * k⁻¹ * y⁻¹) = 1 := by
      refine (hφ.ker_iff _).mpr ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hx (y : G) y.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem conjSubgroup_le_iff_barSub_le (s : TailSetup V H T φ) {a : G} (ha : a ∈ H) :
    conjSubgroup V a ≤ T ↔
      barSub (kGenIn V H) φ (conjSubgroup V a) ≤ barSub (kGenIn V H) φ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := kGenIn V H
  let C := Subgroup.centralizer (eSub V H T : Set G)
  let N := K ⊓ C
  let Sg := T ⊓ K
  let Z := Sg ⊔ N
  have hKH : K ≤ H := kGenIn_le_H s.hyp83.le_H
  have hZK : Z ≤ K := sup_le inf_le_right inf_le_left
  have hXK : conjSubgroup V a ≤ K := conjSubgroup_le_kGenIn_of_mem_H s.hyp83 s.eq_sup ha
  constructor
  · intro hAT
    exact Subgroup.map_mono (fun x hx => hAT hx)
  · intro hbar
    have hXZ : conjSubgroup V a ≤ Z := by
      intro x hx
      have hxK : x ∈ K := hXK hx
      have hφxX : φ ⟨x, hxK⟩ ∈ barSub K φ (conjSubgroup V a) :=
        mem_barSub.mpr ⟨⟨x, hxK⟩, hx, rfl⟩
      obtain ⟨k, hkT, hkφ⟩ := mem_barSub.mp (hbar hφxX)
      have hkSg : (k : G) ∈ Sg := ⟨hkT, k.2⟩
      have hxkN : x * (k : G)⁻¹ ∈ N := by
        refine ⟨K.mul_mem hxK (K.inv_mem k.2), ?_⟩
        have h1 : φ (⟨x, hxK⟩ * k⁻¹) = 1 := by
          rw [map_mul, map_inv, hkφ, mul_inv_cancel]
        have := (s.bar.ker_iff (⟨x, hxK⟩ * k⁻¹)).mp h1
        simpa using this
      have hx_eq : x = (x * (k : G)⁻¹) * (k : G) := by group
      rw [hx_eq]
      exact Z.mul_mem (Subgroup.mem_sup_right hxkN) (Subgroup.mem_sup_left hkSg)
    have hXp : IsPGroup 2 (conjSubgroup V a) :=
      CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
        (isElemAbelian_conjSubgroup' s.hyp83.elemAbelian a)
    have hSgN : Sg ≤ Subgroup.normalizer (N : Set G) := by
      intro x hx
      have hxK : x ∈ K := hx.2
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyK, hyC⟩
        exact ⟨K.mul_mem (K.mul_mem hxK hyK) (K.inv_mem hxK),
          s.hyp83.conj_mem_centralizer_eSub (hKH hxK) hyC⟩
      · rintro ⟨hyK, hyC⟩
        exact ⟨by simpa [mul_assoc] using
            K.mul_mem (K.mul_mem (K.inv_mem hxK) hyK) hxK,
          by simpa [mul_assoc] using
            s.hyp83.conj_mem_centralizer_eSub (H.inv_mem (hKH hxK)) hyC⟩
    have hSylK : IsSylowTwoOf Sg K :=
      s.hyp83.sylow_H.inf_normal hKH
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
          (s.hyp83.le_normalizer_kGenIn_of_eq_sup s.eq_sup))
    have hSylZ : IsSylowTwoOf Sg Z := by
      refine ⟨le_sup_left, hSylK.2.1, fun hh => hSylK.2.2 ?_⟩
      change 2 ∣ Sg.relIndex K
      change 2 ∣ Sg.relIndex Z at hh
      exact hh.trans ⟨_, (Subgroup.relIndex_mul_relIndex Sg Z K le_sup_left hZK).symm⟩
    obtain ⟨x, hxZ, hxX⟩ := exists_conj_le_of_isSylowTwoOf hSylZ hXZ hXp
    obtain ⟨sm, hsmSg, nn, hnnN, h_eq⟩ :=
      w85g_exists_mul_eq_of_mem_sup_of_le_normalizer hSgN hxZ
    have hSg_sm : conjSubgroup Sg sm = Sg :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hsmSg)
    have hcj : cjSub nn (conjSubgroup V a) ≤ Sg := by
      intro y hy
      have hy' : sm * y * sm⁻¹ ∈ cjSub sm (cjSub nn (conjSubgroup V a)) := by
        rw [mem_cjSub]
        simpa [mul_assoc] using hy
      have hsplit : cjSub sm (cjSub nn (conjSubgroup V a)) =
          cjSub (sm * nn) (conjSubgroup V a) := by
        ext z
        simp [cjSub, mul_assoc]
      have hySg : sm * y * sm⁻¹ ∈ Sg := by
        rw [hsplit, h_eq] at hy'
        exact hxX hy'
      have hySg' : y ∈ conjSubgroup Sg sm := by
        rw [mem_conjSubgroup_iff]
        simpa [mul_assoc] using hySg
      rwa [hSg_sm] at hySg'
    have hnnK : nn ∈ K := hnnN.1
    have hnnC : nn ∈ C := hnnN.2
    have hnn1 : φ ⟨nn, hnnK⟩ = 1 := (s.bar.ker_iff ⟨nn, hnnK⟩).mpr hnnC
    have hconj_eq : conjSubgroup V (a * nn⁻¹) = cjSub nn (conjSubgroup V a) := by
      simpa [cjSub, conjSubgroup] using (conjSubgroup_conjSubgroup V a nn⁻¹).symm
    have hImg : barSub K φ (conjSubgroup V a) = barSub K φ (conjSubgroup V (a * nn⁻¹)) := by
      rw [hconj_eq, w85g_barSub_cjSub_eq hnnK hnn1 (conjSubgroup V a)]
    have ha' : a * nn⁻¹ ∈ H := H.mul_mem ha (H.inv_mem (hKH hnnK))
    have hEq := conjSubgroup_eq_of_barSub_eq s ha ha' hImg
    rw [hEq, hconj_eq]
    exact hcj.trans (show Sg ≤ T from inf_le_left)

theorem mem_normalizer_iff_bar (s : TailSetup V H T φ) (k : ↥(kGenIn V H)) :
    (k : G) ∈ Subgroup.normalizer (V : Set G) ↔
      φ k ∈ Subgroup.normalizer (barSub (kGenIn V H) φ V : Set X) := by
  have hkH : (k : G) ∈ H := (kGenIn_le_H s.hyp83.le_H) k.2
  constructor
  · intro hk
    have hconj : conjSubgroup V (k : G) = V := conjSubgroup_eq_iff_mem_normalizer.mpr hk
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← w85g_barSub_conjSubgroup V k, hconj]
  · intro hk
    rw [← conjSubgroup_eq_iff_mem_normalizer] at hk
    have hImg : barSub (kGenIn V H) φ (conjSubgroup V (k : G)) =
        barSub (kGenIn V H) φ V := by
      rw [w85g_barSub_conjSubgroup V k, hk]
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hbar : barSub (kGenIn V H) φ (conjSubgroup V (k : G)) =
        barSub (kGenIn V H) φ (conjSubgroup V (1 : G)) := by
      rw [conjSubgroup_one]
      exact hImg
    simpa [conjSubgroup_one] using conjSubgroup_eq_of_barSub_eq s hkH H.one_mem hbar

theorem weaklyClosed_of_bar (s : TailSetup V H T φ)
    (hwc : ∀ g : X, conjSubgroup (barSub (kGenIn V H) φ V) g ≤ barSub (kGenIn V H) φ T →
      conjSubgroup (barSub (kGenIn V H) φ V) g = barSub (kGenIn V H) φ V) :
    ∀ x ∈ H, conjSubgroup V x ≤ T → conjSubgroup V x = V := by
  intro x hxH hxT
  have hx_sup : x ∈ T ⊔ kGenIn V H := by
    rw [sup_comm]
    rwa [← s.eq_sup]
  obtain ⟨t, htT, k, hkK, hx_eq⟩ :=
    w85g_exists_mul_eq_of_mem_sup_of_le_normalizer s.hyp83.le_normalizer_kGenIn hx_sup
  have htN : t ∈ Subgroup.normalizer (V : Set G) := s.hyp83.T_le_normalizer htT
  have hconjVt : conjSubgroup V t = V := conjSubgroup_eq_iff_mem_normalizer.mpr htN
  have hxkV : conjSubgroup V x = conjSubgroup V k := by
    rw [← hx_eq, ← conjSubgroup_conjSubgroup V t k, hconjVt]
  have hkT : conjSubgroup V k ≤ T := hxkV ▸ hxT
  have hbar_le : barSub (kGenIn V H) φ (conjSubgroup V k) ≤ barSub (kGenIn V H) φ T :=
    (conjSubgroup_le_iff_barSub_le s (kGenIn_le_H s.hyp83.le_H hkK)).mp hkT
  have hwc_k := hwc (φ ⟨k, hkK⟩) (by
    rw [← w85g_barSub_conjSubgroup V ⟨k, hkK⟩]
    exact hbar_le)
  have hImg : barSub (kGenIn V H) φ (conjSubgroup V k) = barSub (kGenIn V H) φ V := by
    rw [w85g_barSub_conjSubgroup V ⟨k, hkK⟩, hwc_k]
  have hbar1 : barSub (kGenIn V H) φ (conjSubgroup V k) =
      barSub (kGenIn V H) φ (conjSubgroup V (1 : G)) := by
    rw [conjSubgroup_one]
    exact hImg
  have hEq := conjSubgroup_eq_of_barSub_eq s (kGenIn_le_H s.hyp83.le_H hkK) H.one_mem hbar1
  rw [conjSubgroup_one] at hEq
  rw [hxkV]
  exact hEq

theorem isWeaklyClosedIn_of_sylow {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    {P Q : Sylow 2 Y} (hP : S ≤ (P : Subgroup Y)) (hQ : S ≤ (Q : Subgroup Y))
    (hw : IsWeaklyClosedIn S (P : Subgroup Y)) : IsWeaklyClosedIn S (Q : Subgroup Y) := by
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P Q
  have hQz : (Q : Subgroup Y) = conjSubgroup (P : Subgroup Y) y⁻¹ := by
    have h1 : (↑(y • P) : Subgroup Y) = conjSubgroup (P : Subgroup Y) y⁻¹ := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      simp only [conjSubgroup, inv_inv]
      exact congrArg (fun f : Y →* Y => (P : Subgroup Y).map f) (by ext x; rfl)
    rw [← h1]
    exact congrArg (fun R : Sylow 2 Y => (R : Subgroup Y)) hy.symm
  have hSy : conjSubgroup S y = S := by
    refine hw y ?_
    have h3 : S ≤ conjSubgroup (P : Subgroup Y) y⁻¹ := by rw [← hQz]; exact hQ
    have h2 : conjSubgroup S y ≤ conjSubgroup (conjSubgroup (P : Subgroup Y) y⁻¹) y :=
      Subgroup.map_mono h3
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
  intro g hg
  have hgy : conjSubgroup S (g * y) = S := by
    refine hw (g * y) ?_
    have h3 : conjSubgroup S g ≤ conjSubgroup (P : Subgroup Y) y⁻¹ := by rw [← hQz]; exact hg
    have h2 : conjSubgroup (conjSubgroup S g) y ≤
        conjSubgroup (conjSubgroup (P : Subgroup Y) y⁻¹) y :=
      Subgroup.map_mono h3
    rw [conjSubgroup_conjSubgroup] at h2
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
  have h1 : conjSubgroup S g = conjSubgroup S y⁻¹ := by
    have := congrArg (fun A => conjSubgroup A y⁻¹) hgy
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one, mul_assoc] using this
  have h2 : S = conjSubgroup S y⁻¹ := by
    have := congrArg (fun A => conjSubgroup A y⁻¹) hSy
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one, mul_assoc] using this
  exact h1.trans h2.symm

theorem exists_central_quotient (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {X₂ : Type}
    [Group X₂] {φ₂ : ↥(kGenIn V H) →* X₂}
    (hφ₂ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ₂) :
    ∃ (Y : Type) (_ : Group Y) (φ : ↥(kGenIn V H) →* Y) (ψ : X₂ →* Y),
      IsBarMap (kGenIn V H) (Subgroup.centralizer (eSub V H T : Set G)) φ ∧
        Function.Surjective ψ ∧ (∀ k, ψ (φ₂ k) = φ k) ∧ ψ.ker ≤ Subgroup.center X₂ := by
  obtain ⟨Y, hYgrp, φ, hφ⟩ := exists_barMap_eCent h hKT
  have hle : φ₂.ker ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [hφ₂.ker_iff] at hk
    rw [hφ.ker_iff]
    exact h.pCoreOf_kGenIn_le_centralizer_eSub hk
  let ψ : X₂ →* Y := MonoidHom.liftOfSurjective φ₂ hφ₂.surjective ⟨φ, hle⟩
  refine ⟨Y, hYgrp, φ, ψ, hφ, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨k, hk⟩ := hφ.surjective y
    exact ⟨φ₂ k, by simpa [ψ] using hk⟩
  · intro k
    simp [ψ]
  · intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨k, hk⟩ := hφ₂.surjective y
    obtain ⟨m, hm⟩ := hφ₂.surjective g
    have hkC : (k : G) ∈ Subgroup.centralizer (eSub V H T : Set G) := by
      have h1 : φ k = 1 := by
        have h2 := hy
        rw [← hk] at h2
        simpa [ψ] using h2
      exact (hφ.ker_iff k).mp h1
    have hcomm : (m : G) * (k : G) * (m : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 (kGenIn V H) := by
      have hmK : (m : G) ∈ kGenIn V H := m.2
      have hc := h.comm_mem_pCoreOf_of_mem_inf_centralizer hKT hkC (m : G) hmK
      have := (pCoreOf 2 (kGenIn V H)).inv_mem hc
      simpa [mul_assoc] using this
    have h1 : φ₂ (m * k) = φ₂ (k * m) := by
      have hmem : m * k * (k * m)⁻¹ ∈ φ₂.ker := by
        rw [MonoidHom.mem_ker, hφ₂.ker_iff]
        simpa [mul_assoc] using hcomm
      have h2 : φ₂ (m * k) * (φ₂ (k * m))⁻¹ = 1 := by
        simpa [map_mul, map_inv] using MonoidHom.mem_ker.mp hmem
      exact mul_inv_eq_one.mp h2
    rw [← hm, ← hk]
    rw [← map_mul, ← map_mul]
    exact h1

theorem nonempty_mulEquiv_of_kBarCenterShape_eCent (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {P : ∀ (Y : Type) [Group Y], Prop} (hP : KBarCenterShape V H T P)
    (hφ : IsBarMap (kGenIn V H) (Subgroup.centralizer (eSub V H T : Set G)) φ) :
    ∃ (Y : Type) (_ : Group Y), P Y ∧ Nonempty ((X ⧸ Subgroup.center X) ≃* Y) := by
  unfold KBarCenterShape at hP
  obtain ⟨Y, hYgrp, ψ, hψsurj, hψker, hPY⟩ := hP
  refine ⟨Y, hYgrp, hPY, ⟨?_⟩⟩
  let ψ₀ : ↥(kGenIn V H) →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp φ
  have hψ₀surj : Function.Surjective ψ₀ :=
    (QuotientGroup.mk'_surjective (Subgroup.center X)).comp hφ.surjective
  have hker : ψ₀.ker = ψ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show ((QuotientGroup.mk' (Subgroup.center X)) (φ k) = 1) ↔ ψ k = 1
    rw [w85g_mk_comp_eq_one_iff_centerPre hφ k, hψker k]
    rfl
  exact ((QuotientGroup.quotientKerEquivOfSurjective (φ := ψ₀) hψ₀surj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψsurj)

private theorem w85g_eq_bot_of_odd_normal_perm {m : ℕ} (hm : 4 ≤ m)
    {N : Subgroup (Equiv.Perm (Fin m))} [hNN : N.Normal] (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  by_contra hbot
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hbot
  have hm1 : Nat.card N ≠ 1 := by
    haveI : Fintype N := Fintype.ofFinite N
    have : 1 < Nat.card N := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hm1
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hpodd : Odd p := Odd.of_dvd_nat hodd hpdvd
  obtain ⟨σN, hσorder⟩ := exists_prime_orderOf_dvd_card' p (by simpa using hpdvd)
  set σ : Equiv.Perm (Fin m) := (σN : Equiv.Perm (Fin m)) with hσdef
  have hσmem : σ ∈ N := σN.2
  have hσorder' : orderOf σ = p := (Subgroup.orderOf_coe σN).trans hσorder
  have hσpow : σ ^ p = 1 := by rw [← hσorder']; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    intro h
    have : p = 1 := by rw [← hσorder', h, orderOf_one]
    exact hpprime.ne_one this
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    simpa using DFunLike.ne_iff.mp hσ1
  have hσ2a : σ (σ a) ≠ a := by
    intro h2
    have hpow : ∀ k, ((σ ^ 2) ^ k) (σ a) = σ a := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ, Equiv.Perm.mul_apply]
        have hstep : (σ ^ 2) (σ a) = σ a := by
          rw [pow_two, Equiv.Perm.mul_apply, h2]
        rw [hstep, ih]
    obtain ⟨k, hk⟩ := hpodd
    have hsp : (σ ^ p) a = a := by rw [hσpow]; rfl
    rw [hk, pow_succ, pow_mul, Equiv.Perm.mul_apply, hpow k] at hsp
    exact ha hsp
  have hdist : σ (σ a) ≠ σ a := by
    intro h
    exact ha (σ.injective h)
  let τ : Equiv.Perm (Fin m) := Equiv.swap a (σ a)
  have hconjσ : σ * τ * σ⁻¹ = Equiv.swap (σ a) (σ (σ a)) := by
    ext x
    by_cases hx1 : x = σ a
    · subst hx1
      simp [τ, Equiv.swap_apply_left, Equiv.swap_apply_right]
    by_cases hx2 : x = σ (σ a)
    · subst hx2
      simp [τ, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · have hx1' : σ⁻¹ x ≠ a := by
        intro h
        apply hx1
        calc x = σ (σ⁻¹ x) := (σ.apply_symm_apply x).symm
          _ = σ a := by rw [h]
      have hx2' : σ⁻¹ x ≠ σ a := by
        intro h
        apply hx2
        calc x = σ (σ⁻¹ x) := (σ.apply_symm_apply x).symm
          _ = σ (σ a) := by rw [h]
      simp only [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx1' hx2',
        Equiv.swap_apply_of_ne_of_ne hx1 hx2]
      exact congrArg Fin.val (Equiv.apply_symm_apply σ x)
  have hc3 : Equiv.Perm.IsThreeCycle ((σ * τ * σ⁻¹) * τ⁻¹) := by
    have hτinv : τ⁻¹ = Equiv.swap a (σ a) := by simp [τ]
    rw [hconjσ, hτinv, Equiv.swap_comm a (σ a)]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hdist.symm ha hσ2a
  have hcN : (σ * τ * σ⁻¹) * τ⁻¹ ∈ N := by
    have hconj : τ * σ⁻¹ * τ⁻¹ ∈ N := hNN.conj_mem σ⁻¹ (N.inv_mem hσmem) τ
    have heq : (σ * τ * σ⁻¹) * τ⁻¹ = σ * (τ * σ⁻¹ * τ⁻¹) := by group
    rw [heq]
    exact N.mul_mem hσmem hconj
  have hthree : ∀ d : Equiv.Perm (Fin m), Equiv.Perm.IsThreeCycle d → d ∈ N := by
    intro d hd
    have hconj : IsConj ((σ * τ * σ⁻¹) * τ⁻¹) d :=
      Equiv.Perm.isConj_of_cycleType_eq (by rw [hc3.cycleType, hd.cycleType])
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact hNN.conj_mem _ hcN g
  have hAle : alternatingGroup (Fin m) ≤ N := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    exact (Subgroup.closure_le N).mpr fun d hd => hthree d hd
  have hdvd : Nat.card (alternatingGroup (Fin m)) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le hAle
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have heven : Even (Nat.card (alternatingGroup (Fin m))) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    have h4 : 4 ∣ m.factorial :=
      dvd_trans (by norm_num [Nat.factorial]) (Nat.factorial_dvd_factorial hm)
    obtain ⟨q, hq⟩ := h4
    refine ⟨q, ?_⟩
    rw [hq]
    have h : 4 * q = 2 * (2 * q) := by ring
    rw [h, Nat.mul_div_cancel_left (2 * q) (by norm_num : 0 < 2)]
    ring
  have hevenN : Even (Nat.card N) := by
    rw [even_iff_two_dvd] at heven ⊢
    exact heven.trans hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) hevenN

theorem isSymGp_quot_fusionOddCore_of_center {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m)
    (hodd : Odd (Nat.card (Subgroup.center Y))) (h : IsSymGp (Y ⧸ Subgroup.center Y) m) :
    IsSymGp (Y ⧸ fusionOddCore Y) m := by
  have hZO : Subgroup.center Y ≤ fusionOddCore Y :=
    CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
  let π : Y ⧸ Subgroup.center Y →* Y ⧸ fusionOddCore Y :=
    QuotientGroup.map (Subgroup.center Y) (fusionOddCore Y) (MonoidHom.id Y)
      (by simpa using hZO)
  obtain ⟨e⟩ := h
  have hker : π.ker = (fusionOddCore Y).map (QuotientGroup.mk' (Subgroup.center Y)) := by
    rw [QuotientGroup.ker_map]
    rfl
  haveI : (π.ker.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (inferInstance : π.ker.Normal) e.toMonoidHom e.surjective
  have hNodd : Odd (Nat.card (π.ker.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective, hker]
    exact Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y)
      (Subgroup.card_map_dvd (H := fusionOddCore Y) (f := QuotientGroup.mk' (Subgroup.center Y)))
  have hNbot : π.ker.map e.toMonoidHom = ⊥ := w85g_eq_bot_of_odd_normal_perm hm hNodd
  have hπker : π.ker = ⊥ := by
    rw [Subgroup.map_eq_bot_iff] at hNbot
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective] at hNbot
    exact le_bot_iff.mp hNbot
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπker
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore Y) y
    exact ⟨(QuotientGroup.mk' (Subgroup.center Y)) x, by
      rw [QuotientGroup.map_mk']
      rfl⟩
  exact ⟨(MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩).symm.trans e⟩

theorem hyp85Three'_of_hyp85Three (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    Hyp85Three V H T → Hyp85Three' V H T := by
  rintro (h1 | h2 | ⟨m, hm, hP⟩)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨m, hm, ?_⟩)
    obtain ⟨Y, _, φ, hφ⟩ := exists_barMap_eCent h hKT
    obtain ⟨Z, _, ⟨e'⟩, ⟨e⟩⟩ := nonempty_mulEquiv_of_kBarCenterShape_eCent h hKT hP hφ
    haveI : Finite Y := Finite.of_surjective φ hφ.surjective
    exact ⟨Y, inferInstance, φ, hφ, isSymGp_quot_fusionOddCore_of_center (by omega)
      (odd_card_center_bar ⟨h, hKT, hφ⟩) ⟨e.trans e'⟩⟩

theorem w3Lem85ThreeFirst_of_prime (hF : W3Lem85ThreeFirst' G) : W3Lem85ThreeFirst G := by
  intro V H T hV hH hH0 hT hKT hyp
  exact hF V H T hV hH hH0 hT hKT
    (hyp85Three'_of_hyp85Three (Hyp83.of_hyp7 hV hH hH0 hT) hKT hyp)

end CFSG.LocalAnalysis.WeakClosure81

end
