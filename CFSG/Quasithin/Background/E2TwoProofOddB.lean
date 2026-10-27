module

public import CFSG.Quasithin.Background.E2TwoProofOddA
public import CFSG.Quasithin.Background.E2TwoProofL3Sp4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6
open scoped MatrixGroups

namespace E2P

section L2

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem conj_injective (hZ : Subgroup.center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro y
  have h := congrArg (fun φ : MulAut L => φ y) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc y * x = x * y * x⁻¹ * x := by rw [h]
    _ = x * y := by group

theorem three_dvd_card_normalizer_four
    {F : Type} [Field F] [Finite F] (hF : GH74.GLS.IVK.L2Field F) (e : L ≃* GH74.GLS.IVK.L2 F)
    (hZ : Subgroup.center L = ⊥) {V : Subgroup L} (hV : IsKleinFour ↥V) :
    3 ∣ Nat.card (Subgroup.normalizer (V : Set L)) := by
  classical
  set c : L →* MulAut L := MulAut.conj with hcdef
  have hc := conj_injective hZ
  set U := V.map c with hU
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥V)
    rw [hV.exponent_two, pow_two] at h
    exact congrArg Subtype.val h
  have hinv : ∀ x ∈ V, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    calc x * y = (x * y)⁻¹ := (hinv _ (V.mul_mem hx hy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv x hx, hinv y hy]
  have hU4 : GH74.GLS.IVK.IsFourSubgroup U := by
    refine ⟨?_, ?_⟩
    · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
      · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← map_mul, ← map_mul, hcomm x hx y hy]
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
        obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        apply Subtype.ext
        simp only [SubmonoidClass.coe_pow, Subgroup.coe_one]
        rw [← map_pow, pow_two, hsq x hx, map_one]
    · rw [Subgroup.card_map_of_injective hc, hV.card_four]
  have h := GH74.GLS.IVK.ivk_1_3f_c F hF L e U (Subgroup.map_le_range c V) hU4
  have hmap : (Subgroup.normalizer (V : Set L)).map c =
      Subgroup.normalizer (U : Set (MulAut L)) ⊓ GH74.GLS.IVK.innAut L := by
    ext φ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(mem_normalizer_map_iff_of_injective hc).mpr hg, ⟨g, rfl⟩⟩
    · rintro ⟨hφN, ⟨g, rfl⟩⟩
      exact ⟨g, (mem_normalizer_map_iff_of_injective hc).mp hφN, rfl⟩
  have hcard : Nat.card (Subgroup.normalizer (V : Set L)) =
      Nat.card ↥(Subgroup.normalizer (U : Set (MulAut L)) ⊓ GH74.GLS.IVK.innAut L) := by
    rw [← hmap, Subgroup.card_map_of_injective hc]
  rw [hcard]
  rcases h with ⟨⟨eA⟩⟩ | ⟨⟨eS⟩⟩
  · rw [Nat.card_congr eA.toEquiv, Goldschmidt.G3b.card_alternatingGroup_four']
    norm_num
  · rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

end L2

section Zeta

variable {X : Type} [Group X]

omit [Group X] in
theorem zOf_comm {G : Type} [Group G] {S : Subgroup G} {w x : G} (hw : w ∈ zOf S) (hx : x ∈ S) :
    w * x = x * w :=
  ((Subgroup.mem_centralizer_iff.mp hw.2) x hx).symm

theorem conj_mem_zOf {S : Subgroup X} {t w : X} (ht : t ∈ Subgroup.normalizer (S : Set X))
    (hw : w ∈ zOf S) : t * w * t⁻¹ ∈ zOf S := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp ht w).mp hw.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have hx' : t⁻¹ * x * t ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) x).mp hx
    simpa using this
  have h := zOf_comm hw hx'
  calc x * (t * w * t⁻¹) = t * ((t⁻¹ * x * t) * w) * t⁻¹ := by group
    _ = t * (w * (t⁻¹ * x * t)) * t⁻¹ := by rw [h]
    _ = t * w * t⁻¹ * x := by group

theorem zOf_eq_map_center (S : Subgroup X) : zOf S = (Subgroup.center ↥S).map S.subtype := by
  ext x
  constructor
  · rintro ⟨hxS, hxC⟩
    refine ⟨⟨x, hxS⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
    exact congrArg Subtype.val this

theorem exists_zOf_eq [Finite X] {S : Subgroup X} (h2 : Nat.card ↥(zOf S) = 2) :
    ∃ z ∈ zOf S, z ≠ 1 ∧ orderOf z = 2 ∧ (∀ w ∈ zOf S, w = 1 ∨ w = z) ∧
      ∀ t ∈ Subgroup.normalizer (S : Set X), t * z * t⁻¹ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hz⟩, hz2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zOf S)) 2 (by rw [h2])
  have hz1 : z ≠ 1 := by
    intro h1
    subst h1
    have : (⟨1, hz⟩ : ↥(zOf S)) = 1 := rfl
    rw [this, orderOf_one] at hz2
    omega
  have hall : ∀ w ∈ zOf S, w = 1 ∨ w = z := by
    intro w hw
    by_contra hcon
    push Not at hcon
    have hsub : ({1, z, w} : Set X) ⊆ (zOf S : Set X) := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact (zOf S).one_mem
      · exact hz
      · exact hw
    have h3 : ({1, z, w} : Set X).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hcon.2)]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1.symm, Ne.symm hcon.1⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3, ← Nat.card_coe_set_eq] at this
    change 3 ≤ Nat.card ↥(zOf S) at this
    omega
  refine ⟨z, hz, hz1, by rw [← Subgroup.orderOf_mk z hz, hz2], hall, fun t ht => ?_⟩
  rcases hall _ (conj_mem_zOf ht hz) with h | h
  · exfalso
    apply hz1
    calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem centralizer_zOf_eq {S : Subgroup X} {z : X} (hz : z ∈ zOf S)
    (hall : ∀ w ∈ zOf S, w = 1 ∨ w = z) :
    Subgroup.centralizer (zOf S : Set X) = Subgroup.centralizer ({z} : Set X) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h z hz).symm
  · intro h w hw
    rcases hall w hw with rfl | rfl
    · group
    · exact h.symm

end Zeta

section Inj

variable {G H : Type} [Group G] [Group H] {f : G →* H}

theorem mem_centralizer_map_iff_of_injective (hf : Function.Injective f) {P : Subgroup G}
    {g : G} :
    f g ∈ Subgroup.centralizer (P.map f : Set H) ↔ g ∈ Subgroup.centralizer (P : Set G) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact hf (by rw [map_mul, map_mul]; exact h (f x) ⟨x, hx, rfl⟩)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h x hx]

theorem isKleinFour_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsKleinFour A) : IsKleinFour B where
  card_four := (Nat.card_congr e.toEquiv).symm.trans h.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv e.symm).trans h.exponent_two

end Inj

theorem sixteen_dvd_sq_sub_one {q : ℕ} (h8 : q % 8 = 1 ∨ q % 8 = 7) : 16 ∣ q ^ 2 - 1 := by
  have h16 : q % 16 = 1 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 15 := by omega
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsq : q ^ 2 % 16 = 1 := by
    rw [Nat.pow_mod]
    rcases h16 with h | h | h | h <;> rw [h]
  omega

section Main

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

namespace ASHyp

variable (hX : ASHyp K T M)
include hX

theorem autCard_eq_card : E2.autCard T K = Nat.card T := by
  unfold E2.autCard
  have hN : Subgroup.normalizer (K : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hX.normal
  rw [hN, hX.cent, inf_top_eq, inf_bot_eq, Subgroup.relIndex_bot_left]

theorem exists_dihedral {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f)
    (e : ↥K ≃* PSL(2, GaloisField p f)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(T ⊓ K) ≃* DihedralGroup (2 ^ m)) := by
  have hS := hX.isSylow_inf
  set S : Sylow 2 ↥K := toSylow2 hS
  have hSc : (S : Subgroup ↥K) = (T ⊓ K).subgroupOf K := toSylow2_coe hS
  have hodd := Walter.isOddPrimePower_of_card (GaloisField.card p f hf.ne') hp hf
  let S' : Sylow 2 PSL(2, GaloisField p f) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup PSL(2, GaloisField p f)) = (S : Subgroup ↥K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨m, hm, ⟨eD⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hodd S'
  refine ⟨m, hm, ⟨?_⟩⟩
  exact ((Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).symm.trans
    ((MulEquiv.subgroupCongr hSc.symm).trans ((Subgroup.equivMapOfInjective _ _ e.injective).trans
      ((MulEquiv.subgroupCongr hS'.symm).trans eD))))

theorem eight_dvd_card_inf {F : Type} [Field F] [Finite F] (hF : GH74.GLS.IVK.L2Field F)
    (e₀ : ↥K ≃* GH74.GLS.IVK.L2 F) (h8 : Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 7) :
    8 ∣ Nat.card ↥(T ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := GH74.GLS.IVK.ivk_1_2b F hF ↥K e₀
  have h16 := E2P.sixteen_dvd_sq_sub_one h8
  have hdvd : 2 ^ 3 ∣ Nat.card ↥K := by
    rw [hK]
    obtain ⟨k, hk⟩ := h16
    rw [hk, show Nat.card F * (16 * k) = 2 * (8 * (Nat.card F * k)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.intro _ rfl
  have hS := hX.isSylow_inf
  have h1 := Sylow.pow_dvd_card_of_pow_dvd_card (toSylow2 hS) hdvd
  rw [toSylow2_coe hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
  simpa using h1

theorem exists_maxParabolic :
    ∃ P : Subgroup X, IsMaxParabolic2 K P ∧
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤ P := by
  set B := (K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)).subgroupOf K with hB
  have hBne : B ≠ ⊤ := by
    intro h
    apply hX.normalizer_ne
    exact le_antisymm inf_le_left fun x hx => (Subgroup.subgroupOf_eq_top.mp h) hx
  obtain ⟨Q, hBQ, hQ⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.mpr hBne)
  have hQc := hQ.isCoatom
  have hPK : Q.map K.subtype ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hNP : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤ Q.map K.subtype :=
    fun x hx => ⟨⟨x, hx.1⟩, hBQ hx, rfl⟩
  have hQP : (Q.map K.subtype).subgroupOf K = Q :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q
  refine ⟨Q.map K.subtype, ⟨⟨hPK, T ⊓ K, hX.isSylow_inf, hNP⟩, ?_, ?_⟩, hNP⟩
  · intro h
    apply hQc.1
    rw [← hQP, h, Subgroup.subgroupOf_self]
  · intro Q' hQ' hQ'ne hPQ'
    have hle : Q ≤ Q'.subgroupOf K := by
      rw [← hQP]
      exact Subgroup.subgroupOf_mono _ hPQ'
    rcases hQc.le_iff.mp hle with h | h
    · exfalso
      apply hQ'ne
      exact le_antisymm hQ'.1 fun x hx => (Subgroup.subgroupOf_eq_top.mp h) hx
    · rw [← Subgroup.map_subgroupOf_eq_of_le hQ'.1, h]

end ASHyp

theorem ASHyp.oddL2_of_one_mod_eight
    (hX : ASHyp K T M) {p f : ℕ} [hpp : Fact p.Prime] (hp : Odd p)
    (h : IsPSL 2 p f ↥K) (h8 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7) (h9 : p ^ f ≠ 9) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) ∧ 8 < E2.autCard T K := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hf, F, hF, hFin, hcard, ⟨e₀⟩, ⟨e⟩⟩ := exists_psl2_galois_equiv h
  have hq7 : 7 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hpp.out.two_le
      rcases hp with ⟨k, hk⟩
      omega
    have : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by omega) p)
    omega
  have hFL : GH74.GLS.IVK.L2Field F := ⟨by rw [hcard]; exact hp.pow, by rw [hcard]; omega⟩
  have hZK := hX.center_eq_bot
  have h8S := hX.eight_dvd_card_inf hFL e₀ (by rw [hcard]; exact h8)
  obtain ⟨m, hm, ⟨eD⟩⟩ := hX.exists_dihedral hp hf e
  have hcardS : Nat.card ↥(T ⊓ K) = 2 ^ (m + 1) := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm2 : 2 ≤ m := by
    rw [hcardS] at h8S
    by_contra hlt
    have : m + 1 ≤ 2 := by omega
    have h4 : 2 ^ (m + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    have := Nat.le_of_dvd (by positivity) h8S
    omega
  have hZ2 : Nat.card ↥(zOf (T ⊓ K)) = 2 := by
    rw [zOf_eq_map_center, Subgroup.card_map_of_injective (T ⊓ K).subtype_injective,
      Nat.card_congr (Subgroup.centerCongr eD).toEquiv]
    exact Walter.card_center_dihedralGroup
      (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2))
      (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  obtain ⟨z, hzZ, hz1, hz2, hall, hnorm⟩ := exists_zOf_eq hZ2
  have hC := centralizer_zOf_eq hzZ hall
  have hTz : ∀ t ∈ T, t * z = z * t := fun t ht => by
    have := hnorm t (hX.le_normalizer_inf ht)
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [this]
  have hzK : z ∈ K := hzZ.1.2
  set z' : ↥K := ⟨z, hzK⟩ with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  set Y := K ⊓ Subgroup.centralizer ({z} : Set X) with hY
  have hSY : T ⊓ K ≤ Y := fun x hx =>
    ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (zOf_comm hzZ hx).symm⟩
  have hYmap : (Subgroup.centralizer ({z'} : Set ↥K)).map K.subtype = Y := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨hxK, hxz⟩
      exact ⟨⟨x, hxK⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxz)), rfl⟩
  have hYne : Y ≠ K := by
    intro hYK
    apply hz1
    have hzc : z' ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : (y : X) ∈ Y := by rw [hYK]; exact y.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
    rw [hZK] at hzc
    exact congrArg Subtype.val ((Subgroup.mem_bot).mp hzc)
  have hYM : Y ≤ M ⊓ K :=
    le_inf (hX.le_M_of_normalized inf_le_left hSY hYne (hX.le_normalizer_centralizer hTz))
      inf_le_left
  have hMY : M ⊓ K ≤ Y := by
    by_cases hq : p ^ f = 7
    ·
      have hpf : p = 7 ∧ f = 1 := by
        have := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7) p
          (by rw [← hq]; exact dvd_pow_self p hf.ne'))
        rcases this with h1 | h1
        · exact absurd h1 hpp.out.one_lt.ne'
        · refine ⟨h1, ?_⟩
          subst h1
          by_contra hf1
          have : 7 ^ 2 ≤ 7 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      obtain ⟨rfl, rfl⟩ := hpf
      have h37 : IsPSL 3 2 1 ↥K :=
        QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven h
      obtain ⟨-, S', hS', hMS'⟩ := hX.l3 h37
      have hSS' : T ⊓ K ≤ Subgroup.normalizer (S' : Set X) :=
        (hX.inf_le_inf_M.trans hMS'.le).trans inf_le_right
      have hp2 : IsPGroup 2 ↥(T ⊓ K ⊔ S') :=
        IsPGroup.to_sup_of_normal_right' hX.isSylow_inf.2.1 hS'.2.1 hSS'
      have h1 := eq_of_isSylowTwoOf_le hS' hp2 le_sup_right (sup_le inf_le_right hS'.1)
      have hle : T ⊓ K ≤ S' := h1 ▸ le_sup_left
      have h2' := eq_of_isSylowTwoOf_le hX.isSylow_inf hS'.2.1 hle hS'.1
      rw [hMS', h2']
      rintro x ⟨hxK, hxN⟩
      refine ⟨hxK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := hnorm x hxN
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [this]
    · have h11 : 11 ≤ p ^ f := by
        rcases h8 with h8 | h8 <;> omega
      have hcoat := GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hFL
        (by rw [hcard]; exact h11) e₀ hz'2
      have hle : Subgroup.centralizer ({z'} : Set ↥K) ≤ (M ⊓ K).subgroupOf K := by
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact hYM (hYmap ▸ ⟨y, hy, rfl⟩)
      rcases hcoat.le_iff.mp hle with h1 | h1
      · exfalso
        apply hX.inf_M_ne
        exact le_antisymm inf_le_right fun x hx => (Subgroup.subgroupOf_eq_top.mp h1) hx
      · intro x hx
        have : (⟨x, hx.2⟩ : ↥K) ∈ (M ⊓ K).subgroupOf K := hx
        rw [h1] at this
        rw [← hYmap]
        exact ⟨_, this, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hC]
    exact le_antisymm hMY hYM
  · rw [hX.autCard_eq_card]
    by_contra hT8
    push Not at hT8
    have hST : Nat.card ↥(T ⊓ K) ≤ Nat.card ↥T := Subgroup.card_le_of_le inf_le_left
    have hm2' : m = 2 := by
      by_contra hne
      have h16 : 2 ^ 4 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hm2'
    have hTS : T ⊓ K = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardS]; omega)
    have hTK : T ≤ K := hTS ▸ inf_le_right
    by_cases hq : p ^ f = 7
    · have hpf : p = 7 ∧ f = 1 := by
        have := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7) p
          (by rw [← hq]; exact dvd_pow_self p hf.ne'))
        rcases this with h1 | h1
        · exact absurd h1 hpp.out.one_lt.ne'
        · refine ⟨h1, ?_⟩
          subst h1
          by_contra hf1
          have : 7 ^ 2 ≤ 7 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      obtain ⟨rfl, rfl⟩ := hpf
      have h37 : IsPSL 3 2 1 ↥K :=
        QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven h
      obtain ⟨hD, -⟩ := hX.l3 h37
      obtain ⟨P, hP, hBP⟩ := hX.exists_maxParabolic
      refine hD P hP hBP fun t ht => Subgroup.le_normalizer (hBP ⟨hTK ht, ?_⟩)
      exact hTS.symm ▸ (hX.le_normalizer_inf ht)
    ·
      obtain ⟨V, hVS, hV4, hzV⟩ :=
        GorensteinWalter.exists_kleinFour_of_dihedral_mulEquiv_containing_involution (T ⊓ K)
          hm eD hzZ.1 ⟨hz1, by rw [← hz2]; exact pow_orderOf_eq_one z⟩
      have hidx : (V.subgroupOf (T ⊓ K)).index = 2 := by
        have h1 := Subgroup.card_mul_index (V.subgroupOf (T ⊓ K))
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv, hV4.card_four,
          hcardS] at h1
        omega
      have hVn := Subgroup.normal_of_index_eq_two hidx
      have hTV : T ≤ Subgroup.normalizer (V : Set X) := by
        rw [← hTS]
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVS).mp hVn
      set V' := V.subgroupOf K with hV'
      have hVK : V ≤ K := hVS.trans inf_le_right
      have hV'4 : IsKleinFour ↥V' :=
        isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVK).symm hV4
      have h3 := three_dvd_card_normalizer_four hFL e₀ hZK hV'4
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer
        (V' : Set ↥K))) 3 h3
      have hgpow : (g : ↥K) ^ 3 = 1 := by
        rw [← Subgroup.orderOf_coe] at hg3
        rw [← hg3]
        exact pow_orderOf_eq_one _
      have hodd := Walter.isOddPrimePower_of_card (GaloisField.card p f hf.ne') hp hf
      have hCV : Subgroup.centralizer (V' : Set ↥K) = V' := by
        have h1 := Goldschmidt.G3b.psl2_centralizer_kleinFour (GaloisField p f) hodd
          (V'.map e.toMonoidHom) (GorensteinWalter.isKleinFour_map_of_injective V' hV'4
            e.toMonoidHom e.injective)
        ext x
        rw [← mem_centralizer_map_iff_of_injective (f := e.toMonoidHom) e.injective, h1]
        exact Subgroup.mem_map_iff_mem e.injective
      have hz'V : z' ∈ V' := Subgroup.mem_subgroupOf.mpr hzV
      have hz'1 : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
      have hmove : g.1 * z' * g.1⁻¹ ≠ z' := by
        intro hfix
        have hcen := fixes_of_fixes_four hV'4 g.2 hgpow hz'V hz'1 hfix
        have hgC : g.1 ∈ Subgroup.centralizer (V' : Set ↥K) := by
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          have := hcen x hx
          calc x * g.1 = (g.1 * x * g.1⁻¹) * g.1 := by rw [this]
            _ = g.1 * x := by group
        rw [hCV] at hgC
        have hg2 : g.1 ^ 2 = 1 := by
          have h := Monoid.pow_exponent_eq_one (⟨g.1, hgC⟩ : ↥V')
          rw [hV'4.exponent_two] at h
          exact congrArg Subtype.val h
        have hdvd : orderOf g.1 ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
        rw [Subgroup.orderOf_coe, hg3] at hdvd
        omega
      set Y₁ := (Subgroup.normalizer (V' : Set ↥K)).map K.subtype with hY₁
      have hV'map : V'.map K.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVK
      have hTY₁ : T ≤ Y₁ := by
        intro t ht
        refine ⟨⟨t, hTK ht⟩, ?_, rfl⟩
        have h1 : K.subtype ⟨t, hTK ht⟩ ∈ Subgroup.normalizer ((V'.map K.subtype : Subgroup X) :
            Set X) := by
          rw [hV'map]
          exact hTV ht
        exact (mem_normalizer_map_iff_of_injective K.subtype_injective).mp h1
      have hY₁K : Y₁ ≤ K := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have hY₁ne : Y₁ ≠ K := by
        intro hY
        have htop : Subgroup.normalizer (V' : Set ↥K) = ⊤ := by
          apply Subgroup.map_injective K.subtype_injective
          rw [Subgroup.map_top, Subgroup.range_subtype]
          exact hY
        have hVn' : V'.Normal := Subgroup.normalizer_eq_top_iff.mp htop
        have := hX.simple
        rcases hVn'.eq_bot_or_eq_top with hb | ht
        · have h4 := hV'4.card_four
          rw [hb, Subgroup.card_bot] at h4
          omega
        · have h4 := hV'4.card_four
          rw [ht, Subgroup.card_top, GH74.GLS.IVK.ivk_1_2b F hFL ↥K e₀, hcard] at h4
          have h49 : 49 ≤ (p ^ f) ^ 2 := by nlinarith
          have : 7 * 48 ≤ p ^ f * ((p ^ f) ^ 2 - 1) :=
            Nat.mul_le_mul hq7 (by omega)
          omega
      have h11 : 11 ≤ p ^ f := by
        rcases h8 with h8 | h8 <;> omega
      have hcoat := GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hFL
        (by rw [hcard]; exact h11) e₀ hz'2
      have hgY₁ : (g.1 : X) ∈ Y₁ := ⟨g.1, g.2, rfl⟩
      have hgen : K ≤ Y₁ ⊔ Y := by
        have hle : Subgroup.centralizer ({z'} : Set ↥K) ≤ (Y₁ ⊔ Y).subgroupOf K := by
          intro y hy
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_sup_right (hYmap ▸ ⟨y, hy, rfl⟩)
        have hne : (Y₁ ⊔ Y).subgroupOf K ≠ Subgroup.centralizer ({z'} : Set ↥K) := by
          intro heq
          have hg' : g.1 ∈ (Y₁ ⊔ Y).subgroupOf K :=
            Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hgY₁)
          rw [heq, Subgroup.mem_centralizer_singleton_iff] at hg'
          apply hmove
          rw [hg', mul_inv_cancel_right]
        rcases hcoat.le_iff.mp hle with h1 | h1
        · intro x hx
          have : (⟨x, hx⟩ : ↥K) ∈ (Y₁ ⊔ Y).subgroupOf K := by rw [h1]; trivial
          exact this
        · exact absurd h1 hne
      exact hX.false_of_pair hY₁K inf_le_left (inf_le_left.trans hTY₁) hSY hY₁ne hYne
        (hTY₁.trans (Subgroup.le_normalizer)) (hX.le_normalizer_centralizer hTz) hgen

end Main

end E2P

end CFSG.Quasithin
