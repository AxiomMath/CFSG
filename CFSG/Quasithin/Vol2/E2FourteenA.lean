module

public import CFSG.Quasithin.Vol2.E2ThirteenMembers
public import CFSG.Quasithin.Vol2.E2SevenPairN
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped commutatorElement

theorem exists_mem_ne_of_two_lt_card {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : 2 < Nat.card K) (v : Y) : ∃ w ∈ K, w ≠ 1 ∧ w ≠ v := by
  by_contra hne
  push Not at hne
  have hsub : (K : Set Y) ⊆ {1, v} := by
    intro w hw
    by_cases h1 : w = 1
    · exact Or.inl h1
    · exact Or.inr (hne w hw h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, v} : Set Y).ncard ≤ 2 :=
    (Set.ncard_insert_le 1 {v}).trans (by rw [Set.ncard_singleton])
  have h3 : Nat.card K = (K : Set Y).ncard := Nat.card_coe_set_eq (K : Set Y)
  omega

theorem card_le_two_of_isPGroup_dihedral {X : Type} [Group X] [Finite X] {m : ℕ} (hm : Odd m)
    (e : X ≃* DihedralGroup m) {S : Subgroup X} (hS : IsPGroup 2 S) : Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hS
  have hdvd : Nat.card S ∣ 2 * m := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card S
  rw [hj] at hdvd ⊢
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j <;> norm_num
  · exfalso
    obtain ⟨d, hd⟩ := (Nat.pow_dvd_pow 2 hj2).trans hdvd
    obtain ⟨c, hc⟩ := hm
    norm_num at hd
    omega

theorem exists_conj_of_mem_center {X : Type} [Group X] [Finite X] {k : ℕ} (hk : 2 ≤ k)
    (hX : IsPSL 2 2 k X ∨ IsSz k X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set X)) = 2 ^ k ∧
      ∀ z₁ ∈ S ⊓ Subgroup.centralizer (S : Set X), ∀ z₂ ∈ S ⊓ Subgroup.centralizer (S : Set X),
        z₁ ≠ 1 → z₂ ≠ 1 → ∃ n ∈ Subgroup.normalizer (S : Set X), n⁻¹ * z₁ * n = z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hB⟩ := exists_fusionBenderBorel_of_psl_or_sz hk hX
  have hB' : fusionBenderBorel ↥(⊤ : Subgroup X) (2 ^ k) j :=
    hB.map_mulEquiv Subgroup.topEquiv.symm
  obtain ⟨hcard, hsq⟩ := card_inf_centralizer_of_fusionBenderBorel hB' hS
  refine ⟨hcard, fun z₁ hz₁ z₂ hz₂ h₁ h₂ => ?_⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hSE := (hB (hS.2.1.toSylow hidx)).1
  exact CFSG.ComponentClassification.AschbacherToolkit.Bender.normalizer_transitive_center hSE hsq
    hz₁ hz₂ h₁ h₂

section Star

variable {G : Type} [Group G]

theorem card_star_of_le {M' I X : Subgroup G} (hXI : X ≤ I) :
    Nat.card ↥(star M' I X) = (kerIn M' I ⊓ X).relIndex X := by
  rw [Subgroup.inf_relIndex_right, E2P.star_def, ← Subgroup.relIndex_ker, E2P.ker_starMap,
    Subgroup.relIndex_subgroupOf hXI]

theorem star_le_normalizer_star {M' I K V : Subgroup G}
    (hK : K ⊓ I ≤ Subgroup.normalizer (V : Set G)) :
    star M' I K ≤ Subgroup.normalizer (star M' I V : Set (StarQuot M' I)) := by
  rw [E2P.star_def, E2P.star_def]
  refine le_trans (Subgroup.map_mono fun x hx => ?_) (Subgroup.le_normalizer_map _)
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hK ⟨hx, x.2⟩) y

theorem star_ne_bot_of_gen {M' I V : Subgroup G} {g : G} (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) [Nontrivial (StarQuot M' I)] : star M' I V ≠ ⊥ := by
  intro hV
  have hVJ : V ≤ kerIn M' I := by
    intro v hv
    have hvI : v ∈ I := by
      rw [hgen]
      exact Subgroup.mem_sup_left hv
    have h1 : QuotientGroup.mk' ((kerIn M' I).subgroupOf I) (⟨v, hvI⟩ : I) ∈ star M' I V :=
      ⟨⟨v, hvI⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rw [hV, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  have hWJ : B6.conjSub g V ≤ kerIn M' I := by
    intro x hx
    have h1 := hVJ (mem_conjSub.mp hx)
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M' I hg) _).mp h1
    simpa [mul_assoc] using h2
  have hIJ : ∀ x : I, QuotientGroup.mk' ((kerIn M' I).subgroupOf I) x = 1 := by
    intro x
    have hx : (x : G) ∈ V ⊔ B6.conjSub g V := by
      rw [← hgen]
      exact x.2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact sup_le hVJ hWJ hx
  obtain ⟨a, b, hab⟩ := exists_pair_ne (StarQuot M' I)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  exact hab (by rw [hIJ a', hIJ b'])

theorem star_eq_normalizer_of_isBorelIn [Finite G] {T M I : Subgroup G} (hTM : T ⊓ I ≤ M ⊓ I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hB : IsBorelIn ⊤ (star (M ⊓ I) I (M ⊓ I))) :
    star (M ⊓ I) I (M ⊓ I) =
      Subgroup.normalizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨S, hSsyl, hSeq⟩ := hB
  have hTM' : star (M ⊓ I) I (T ⊓ I) ≤ star (M ⊓ I) I (M ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hTM)
  have hSB : S ≤ star (M ⊓ I) I (M ⊓ I) := by
    rw [hSeq]
    exact le_inf le_top Subgroup.le_normalizer
  have hBN : star (M ⊓ I) I (M ⊓ I) ≤ Subgroup.normalizer (S : Set (StarQuot (M ⊓ I) I)) := by
    rw [hSeq]
    exact inf_le_right
  have hTS : star (M ⊓ I) I (T ⊓ I) ≤ S :=
    le_of_normal_sylow' (B6.isSylowTwoOf_mono hSsyl hSB le_top) hBN hTM' hS.2.1
  have hTeq : star (M ⊓ I) I (T ⊓ I) = S := by
    obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hS hSsyl
    refine Subgroup.eq_of_le_of_card_ge hTS ?_
    rw [hc]
    exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).le
  rw [hSeq, hTeq, top_inf_eq]

end Star

section OneSix

variable {G : Type} [Group G]

theorem inf_eq_inf_normalizer_of_central {I M V Z : Subgroup G} (hVM : IsTISetIn V M)
    (hNV : I ⊓ Subgroup.normalizer (V : Set G) ≤ M) (hZ1 : Z ≠ ⊥) (hZV : Z ≤ V)
    (hZc : ∀ z ∈ Z, ∀ x ∈ I, z * x = x * z) :
    M ⊓ I = I ⊓ Subgroup.normalizer (V : Set G) := by
  apply le_antisymm
  · rintro m ⟨hmM, hmI⟩
    refine ⟨hmI, ?_⟩
    by_contra hmN
    apply hZ1
    rw [eq_bot_iff, ← hVM.2 m hmM hmN]
    intro z hz
    refine ⟨hZV hz, mem_conjSubgroup_iff.mpr ?_⟩
    rw [← hZc z hz m hmI, mul_inv_cancel_right]
    exact hZV hz
  · exact le_inf hNV inf_le_left

theorem autI_le_normalizer_autI {V I A P : Subgroup G} (hV : IsElemAbelian 2 V)
    (hPI : I ≤ Subgroup.normalizer (P : Set G)) (hAP : autI hV A = autI hV P) :
    autI hV I ≤ Subgroup.normalizer (autI hV A : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  obtain ⟨⟨i, hiN⟩, hiI, rfl⟩ := (mem_autI hV).1 hφ
  have hcj : cjSub i P = P := by
    refine le_antisymm (cjSub_le (hPI hiI) le_rfl) fun x hx => ?_
    rw [mem_cjSub]
    exact (Subgroup.mem_normalizer_iff''.mp (hPI hiI) x).mp hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hAP]
  have := autI_cjSub hV hiN P
  rw [hcj] at this
  exact this

end OneSix

section Two

variable {G : Type} [Group G] [Finite G]

namespace Pair

variable {X T M V : Subgroup G} {g : G}

omit [Finite G] in
theorem Vbar_le_commutator (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal]
    (hV : ∀ v ∈ V, v ∉ kerIn M X → ∃ u ∈ V, ∃ n ∈ X ⊓ Subgroup.normalizer (V : Set G),
      (u * v)⁻¹ * (n⁻¹ * u * n) ∈ kerIn M X) :
    Vbar M V X g ≤ commutator (Xbar M V X g) := by
  rintro _ ⟨⟨v, hvX⟩, hv, rfl⟩
  replace hv : v ∈ V := hv
  by_cases hvJ : v ∈ kerIn M X
  · have h1 : QuotientGroup.mk' ((PP M V X g).subgroupOf X) (⟨v, hvX⟩ : X) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left ⟨hvJ, hv⟩
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨u, hu, n, ⟨hnX, hnN⟩, hj⟩ := hV v hv hvJ
  have huX : u ∈ X := h.V_le hu
  have hc : n⁻¹ * u * n ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hnN) u).mp
      hu
    simpa using this
  have hjV : (u * v)⁻¹ * (n⁻¹ * u * n) ∈ V := V.mul_mem (V.inv_mem (V.mul_mem hu hv)) hc
  set q := QuotientGroup.mk' ((PP M V X g).subgroupOf X) with hq
  have key : q ⟨v, hvX⟩ = q ((⟨u, huX⟩ : X)⁻¹ * (⟨n, hnX⟩ : X)⁻¹ * ⟨u, huX⟩ * ⟨n, hnX⟩) := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have e : ((((⟨v, hvX⟩ : X)⁻¹ * ((⟨u, huX⟩ : X)⁻¹ * (⟨n, hnX⟩ : X)⁻¹ * ⟨u, huX⟩ *
        ⟨n, hnX⟩) : X)) : G) = (u * v)⁻¹ * (n⁻¹ * u * n) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mem_sup_left ⟨hj, hjV⟩
  have hcomm := Subgroup.commutator_mem_commutator (Subgroup.mem_top (q ⟨u, huX⟩)⁻¹)
    (Subgroup.mem_top (q ⟨n, hnX⟩)⁻¹)
  rw [commutatorElement_def, inv_inv, inv_inv] at hcomm
  rw [key, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hcomm

end Pair

theorem star_eq_center_of_dihedral {T M V I : Subgroup G} {g : G}
    (hp : Pair I (T ⊓ I) (M ⊓ I) V g) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hVZ : star (M ⊓ I) I V ≤
      Subgroup.centralizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)))
    {m : ℕ} (hm : Odd m) (d : StarQuot (M ⊓ I) I ≃* DihedralGroup m) :
    Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I ∧ star (M ⊓ I) I V = ASInputs.e214ZT T M I := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hidx := hp.relIndex_eq_two_of_dihedral hm d
  obtain ⟨hPO, hOJ, -⟩ := hp.e2_10_six hidx
  refine ⟨hPO.trans hOJ, ?_⟩
  have hVT : star (M ⊓ I) I V ≤ star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hle : star (M ⊓ I) I V ≤ ASInputs.e214ZT T M I := le_inf hVT hVZ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_star_of_le hp.V_le, hidx]
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  exact (Subgroup.card_le_of_le inf_le_left).trans (card_le_two_of_isPGroup_dihedral hm d hS.2.1)

theorem star_eq_center_of_psl_or_sz
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    {T M V I : Subgroup G} {g : G} (hp : Pair I (T ⊓ I) (M ⊓ I) V g)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hTMI : T ⊓ I ≤ M ⊓ I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : star (M ⊓ I) I V ≤
      Subgroup.centralizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)))
    (hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G))
    (hBorel : IsBorelIn ⊤ (star (M ⊓ I) I (M ⊓ I))) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (StarQuot (M ⊓ I) I) ∨ IsSz k (StarQuot (M ⊓ I) I)) :
    (Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I ∨ IsSz 3 (StarQuot (M ⊓ I) I)) ∧
      star (M ⊓ I) I V = ASInputs.e214ZT T M I := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨hcard, htrans⟩ := exists_conj_of_mem_center hk hY hS
  have hBor := star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel
  have hN : star (M ⊓ I) I (M ⊓ I) ≤
      Subgroup.normalizer (star (M ⊓ I) I V : Set (StarQuot (M ⊓ I) I)) :=
    star_le_normalizer_star (inf_le_left.trans hMN)
  have hs : IsSimpleGroup (StarQuot (M ⊓ I) I) := isSimpleGroup_of_psl_or_sz hY
  have hV1 : star (M ⊓ I) I V ≠ ⊥ := star_ne_bot_of_gen hg hgen
  have hVT : star (M ⊓ I) I V ≤ star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hle : star (M ⊓ I) I V ≤ ASInputs.e214ZT T M I := le_inf hVT hVZ
  have hVeq : star (M ⊓ I) I V = ASInputs.e214ZT T M I := by
    refine le_antisymm hle fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ star (M ⊓ I) I V, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hV1 (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
    obtain ⟨n, hn, hnz⟩ := htrans v (hle hv) z hz hv1 hz1
    have hnM : n ∈ star (M ⊓ I) I (M ⊓ I) := by
      rw [hBor]
      exact hn
    have h2 := (Subgroup.mem_normalizer_iff.mp (hN ((star (M ⊓ I) I (M ⊓ I)).inv_mem hnM)) v).mp
      hv
    rw [inv_inv, hnz] at h2
    exact h2
  refine ⟨?_, hVeq⟩
  have hcard' : Nat.card ↥(ASInputs.e214ZT T M I) = 2 ^ k := hcard
  have hc4 : 2 < Nat.card ↥(star (M ⊓ I) I V) := by
    rw [hVeq, hcard']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := hp.normal_P
  obtain ⟨hcase, -⟩ := hp.center_commutator_seven hKG1 hKG3 (by omega : 1 < k) hY
  rcases hcase with hZL | ⟨hSz3, -⟩
  swap
  · exact Or.inr hSz3
  refine Or.inl ?_
  have hVbar : Pair.Vbar (M ⊓ I) V I g ≤ commutator (Pair.Xbar (M ⊓ I) V I g) := by
    refine hp.Vbar_le_commutator fun v hv hvJ => ?_
    have hvI : v ∈ I := hp.V_le hv
    set sq := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hsq
    have hvs : sq ⟨v, hvI⟩ ∈ star (M ⊓ I) I V := ⟨⟨v, hvI⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    have hv1 : sq ⟨v, hvI⟩ ≠ 1 := by
      rw [hsq, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hvJ
    obtain ⟨w, hw, hw1, hwv⟩ := exists_mem_ne_of_two_lt_card hc4 (sq ⟨v, hvI⟩)
    obtain ⟨⟨u, huI⟩, hu, rfl⟩ := hw
    replace hu : u ∈ V := hu
    have hus : sq ⟨u, huI⟩ ∈ star (M ⊓ I) I V := ⟨⟨u, huI⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
    have huv : sq ⟨u, huI⟩ * sq ⟨v, hvI⟩ ∈ star (M ⊓ I) I V := Subgroup.mul_mem _ hus hvs
    have huv1 : sq ⟨u, huI⟩ * sq ⟨v, hvI⟩ ≠ 1 := by
      intro h1
      apply hwv
      have hv2 := sq_eq_one_of_mem_star hp.elem hvs
      calc sq ⟨u, huI⟩ = sq ⟨u, huI⟩ * (sq ⟨v, hvI⟩ * sq ⟨v, hvI⟩) := by rw [hv2, mul_one]
        _ = (sq ⟨u, huI⟩ * sq ⟨v, hvI⟩) * sq ⟨v, hvI⟩ := by group
        _ = sq ⟨v, hvI⟩ := by rw [h1, one_mul]
    obtain ⟨n, hn, hnz⟩ := htrans _ (hle hus) _ (hle huv) hw1 huv1
    have hnM : n ∈ star (M ⊓ I) I (M ⊓ I) := by
      rw [hBor]
      exact hn
    obtain ⟨⟨n₀, hn₀I⟩, hn₀, rfl⟩ := hnM
    replace hn₀ : n₀ ∈ M ⊓ I := hn₀
    refine ⟨u, hu, n₀, ⟨hn₀I, hMN hn₀⟩, ?_⟩
    have hnz' : sq ((⟨n₀, hn₀I⟩ : I)⁻¹ * ⟨u, huI⟩ * ⟨n₀, hn₀I⟩) = sq (⟨u, huI⟩ * ⟨v, hvI⟩) := by
      rw [map_mul, map_mul, map_mul, map_inv]
      exact hnz
    rw [hsq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hnz'
    have e : ((((⟨n₀, hn₀I⟩ : I)⁻¹ * ⟨u, huI⟩ * ⟨n₀, hn₀I⟩)⁻¹ * (⟨u, huI⟩ * ⟨v, hvI⟩) : I) : G) =
        ((u * v)⁻¹ * (n₀⁻¹ * u * n₀))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at hnz'
    have h3 := (kerIn (M ⊓ I) I).inv_mem hnz'
    rw [inv_inv] at h3
    exact h3
  have htop : (⊤ : Subgroup (Pair.Xbar (M ⊓ I) V I g)) = commutator (Pair.Xbar (M ⊓ I) V I g) :=
    le_antisymm (hp.top_eq_commutator_sup_Vbar.le.trans (sup_le le_rfl hVbar)) le_top
  have hZX : Subgroup.center (Pair.Xbar (M ⊓ I) V I g) = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have hzc : z ∈ commutator (Pair.Xbar (M ⊓ I) V I g) := htop ▸ Subgroup.mem_top z
    have hz' : (⟨z, hzc⟩ : commutator (Pair.Xbar (M ⊓ I) V I g)) ∈
        Subgroup.center (commutator (Pair.Xbar (M ⊓ I) V I g)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hz) w)
    rw [hZL, Subgroup.mem_bot] at hz'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hz')
  have hJb := (hp.center_seven hKG1 hKG3 (by omega : 1 < k) hY).1
  rw [hZX] at hJb
  refine le_antisymm hp.P_le_J fun j hj => ?_
  have hjI : j ∈ I := kerIn_le.trans hp.le_X hj
  have h1 : QuotientGroup.mk' ((Pair.PP (M ⊓ I) V I g).subgroupOf I) (⟨j, hjI⟩ : I) ∈
      Pair.Jbar (M ⊓ I) V I g := ⟨⟨j, hjI⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
  rw [← hJb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  exact h1

end Two

end E2

theorem ASInputs.e2_14_one_two_six
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G} (h : E2.Hyp28 H T M V)
    (hTI : IsTISetIn V M) (hI : ASInputs.IsInIHTVC H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hZ : V ⊓ B6.conjSub g V ≠ ⊥)
    (hD : ASInputs.IsDihL2Sz (E2.StarQuot (M ⊓ I) I)) :
    M ⊓ I = I ⊓ Subgroup.normalizer (V : Set G) ∧
      ((ASInputs.e214P V I g = kerIn (M ⊓ I) I ∨ IsSz 3 (E2.StarQuot (M ⊓ I) I)) ∧
        E2.star (M ⊓ I) I V = ASInputs.e214ZT T M I) ∧
      autI h.elem I ≤ Subgroup.normalizer (autI h.elem (ASInputs.e214A V I g) : Set _) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨hp, hVZ, -⟩ := ASInputs.e2_11C_of_not_S6 hKG1 hKG3 h
    (ASInputs.isInIHTVNoRoot_of_isInIHTVC hI) (E2.isEmpty_perm_six_of_isDihL2Sz hD) hg hgen
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have hPeq : ASInputs.e214P V I g = E2.Pair.PP (M ⊓ I) V I g := by
    show B6.conjSub g V ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V)
    rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
  have h1 : M ⊓ I = I ⊓ Subgroup.normalizer (V : Set G) :=
    E2.inf_eq_inf_normalizer_of_central hTI (hp.normalizer_le.trans inf_le_left) hZ inf_le_left
      fun z hz x hx => hp.mem_center hz hx
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G) := h1.le.trans inf_le_right
  have h6 : autI h.elem I ≤ Subgroup.normalizer
      (autI h.elem (ASInputs.e214A V I g) : Set (MulAut (IntMod V h.elem))) := by
    have hAN : B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) ≤ Subgroup.normalizer (V : Set G) :=
      hp.A_le_pCoreOf.trans hp.pCoreOf_le_normalizer
    have hBN : kerIn (M ⊓ I) I ⊓ V ≤ Subgroup.normalizer (V : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    have hBC : kerIn (M ⊓ I) I ⊓ V ≤ Subgroup.centralizer (V : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun v hv => hp.comm hv hb.2
    refine E2.autI_le_normalizer_autI h.elem hp.le_normalizer_P ?_
    rw [show ASInputs.e214A V I g = B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) from
      hp.conjSub_kerIn_inf_eq.symm, autI_sup h.elem hBN hAN,
      autI_eq_bot_of_le_centralizer h.elem hBC, bot_sup_eq]
  refine ⟨h1, ?_, h6⟩
  rw [hPeq]
  rcases hD with ⟨m, hm, -, ⟨d⟩⟩ | hY
  ·
    obtain ⟨hPJ, hV⟩ := E2.star_eq_center_of_dihedral hp hsyl hVZ hm d
    exact ⟨Or.inl hPJ, hV⟩
  obtain ⟨k, hk, hY⟩ : ∃ k, 2 ≤ k ∧ (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨
      IsSz k (E2.StarQuot (M ⊓ I) I)) := by
    rcases hY with ⟨k, hP⟩ | ⟨k, hS⟩
    · exact ⟨k, E2.two_le_of_isPSL hP, Or.inl hP⟩
    · exact ⟨k, by have := (E2.card_of_isSz hS).1; omega, Or.inr hS⟩
  have hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) := by
    obtain ⟨-, -, -, -, k', -, hc⟩ := hI
    rcases hc with ⟨-, -, hB⟩ | ⟨-, p, a, hp', hp2, -, ⟨e⟩⟩ | ⟨-, -, -, hB, -⟩
    · exact hB
    ·
      exfalso
      have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
      obtain ⟨hcard, -⟩ := E2.exists_conj_of_mem_center hk hY hS
      have h2 := E2.card_le_two_of_isPGroup_dihedral (hp'.odd_of_ne_two hp2).pow e hS.2.1
      have h3 := Subgroup.card_le_of_le (inf_le_left : E2.star (M ⊓ I) I (T ⊓ I) ⊓
        Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ≤
          E2.star (M ⊓ I) I (T ⊓ I))
      rw [hcard] at h3
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    · exact hB
  exact E2.star_eq_center_of_psl_or_sz hKG1 hKG3 hp hsyl hTMI hg hgen hVZ hMN hBorel hk hY

end CFSG.Quasithin
