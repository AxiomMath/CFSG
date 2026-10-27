module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Subdirect
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6Gen

variable {G : Type u} [Group G] [Finite G]

open Classical in
noncomputable def crd (K J : Subgroup G) (y : G) : G :=
  if h : IsSemisimple K ∧ J ∈ lcal K ∧ y ∈ K then
    ((h.1.isDirectProduct_lcal.coord h.2.1 ⟨y, h.2.2⟩ : J) : G) else 1

section Crd

variable {K J : Subgroup G} {y z x : G}

theorem crd_eq (hK : IsSemisimple K) (hJ : J ∈ lcal K) (hy : y ∈ K) :
    crd K J y = ((hK.isDirectProduct_lcal.coord hJ ⟨y, hy⟩ : J) : G) := by
  simp [crd, hK, hJ, hy]

theorem crd_mem (hK : IsSemisimple K) (hJ : J ∈ lcal K) (hy : y ∈ K) : crd K J y ∈ J := by
  rw [crd_eq hK hJ hy]
  exact (hK.isDirectProduct_lcal.coord hJ ⟨y, hy⟩).2

theorem crd_mul (hK : IsSemisimple K) (hJ : J ∈ lcal K) (hy : y ∈ K) (hz : z ∈ K) :
    crd K J (y * z) = crd K J y * crd K J z := by
  rw [crd_eq hK hJ hy, crd_eq hK hJ hz, crd_eq hK hJ (mul_mem hy hz)]
  have : (⟨y * z, mul_mem hy hz⟩ : K) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
  rw [this, map_mul]
  rfl

theorem crd_inv (hK : IsSemisimple K) (hJ : J ∈ lcal K) (hy : y ∈ K) :
    crd K J y⁻¹ = (crd K J y)⁻¹ := by
  rw [crd_eq hK hJ hy, crd_eq hK hJ (inv_mem hy)]
  have : (⟨y⁻¹, inv_mem hy⟩ : K) = (⟨y, hy⟩ : K)⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem crd_of_mem (hK : IsSemisimple K) (hJ : J ∈ lcal K) (hx : x ∈ J) : crd K J x = x := by
  have hxK : x ∈ K := hK.isDirectProduct_lcal.le hJ hx
  rw [crd_eq hK hJ hxK]
  exact hK.isDirectProduct_lcal.coord_of_mem hJ hx

theorem crd_eq_one_iff (hK : IsSemisimple K) (hJ : J ∈ lcal K) (hy : y ∈ K) :
    crd K J y = 1 ↔ y ∈ sSup (lcal K \ {J}) := by
  rw [crd_eq hK hJ hy]
  have := hK.isDirectProduct_lcal.coord_eq_one_iff hJ ⟨y, hy⟩
  constructor
  · intro h
    exact this.mp (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (this.mpr h)

theorem crd_conj (hK : IsSemisimple K) (hJ : J ∈ lcal K) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hy : y ∈ K) :
    crd K (J.map (MulAut.conj a).toMonoidHom) (a * y * a⁻¹) = a * crd K J y * a⁻¹ := by
  have ha' : ∀ J ∈ lcal K, J.map (MulAut.conj a).toMonoidHom ∈ lcal K :=
    fun J hJ => map_conj_mem_lcal hJ ha
  have hyK : a * y * a⁻¹ ∈ K := hK.isDirectProduct_lcal.conj_mem ha' hy
  rw [crd_eq hK (ha' J hJ) hyK, crd_eq hK hJ hy]
  exact hK.isDirectProduct_lcal.coord_conj ha' hJ hy

theorem mem_projIn_iff_crd (hK : IsSemisimple K) (hJ : J ∈ lcal K) {X : Subgroup G} {x : G} :
    x ∈ projIn (lcal K) J X ↔ ∃ y ∈ K, y ∈ X ∧ crd K J y = x := by
  rw [hK.isDirectProduct_lcal.mem_projIn_iff hJ]
  constructor
  · rintro ⟨y, hyX, hyx⟩
    exact ⟨y, y.2, hyX, by rw [crd_eq hK hJ y.2]; exact hyx⟩
  · rintro ⟨y, hyK, hyX, hyx⟩
    exact ⟨⟨y, hyK⟩, hyX, by rw [← crd_eq hK hJ hyK]; exact hyx⟩

end Crd


omit [Finite G] in
theorem mem_of_zpow_mem {p : ℕ} (hp : p.Prime) {b : G} (hbp : b ^ p = 1) {H : Subgroup G}
    {i : ℤ} (hi : ¬ (p : ℤ) ∣ i) (h : b ^ i ∈ H) : b ∈ H := by
  have hcop : IsCoprime i (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact (Int.gcd_comm _ _).trans (by
      have := (Int.isCoprime_iff_gcd_eq_one).mp ((Prime.coprime_iff_not_dvd hp').mpr hi).symm
      simpa [Int.gcd_comm] using this)
  obtain ⟨u, v, huv⟩ := hcop
  have : b = (b ^ i) ^ u := by
    calc b = b ^ (u * i + v * p) := by rw [huv, zpow_one]
      _ = b ^ (i * u + (p : ℤ) * v) := by rw [mul_comm u i, mul_comm v (p : ℤ)]
      _ = (b ^ i) ^ u * (b ^ (p : ℤ)) ^ v := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = (b ^ i) ^ u := by rw [zpow_natCast, hbp, one_zpow, mul_one]
  rw [this]
  exact zpow_mem h u


section Norm

variable {K J : Subgroup G}

omit [Finite G] in
theorem zpowers_inf_normalizer_eq_bot {p : ℕ} (hp : p.Prime) {b : G} (hbp : b ^ p = 1)
    (hbJ : b ∉ Subgroup.normalizer (J : Set G)) :
    Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg, hgN⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [Subgroup.mem_bot]
  by_contra hne
  have hi : ¬ (p : ℤ) ∣ i := by
    rintro ⟨k, rfl⟩
    apply hne
    rw [zpow_mul, zpow_natCast, hbp, one_zpow]
  exact hbJ (mem_of_zpow_mem hp hbp hi hgN)

theorem crd_eq_coord_of_mem (hK : IsSemisimple K) {S : Set (Subgroup G)} {L : Subgroup G}
    (hL : IsDirectProduct S L) (hS : S ⊆ lcal K) {J' : Subgroup G} (hJS : J' ∈ S) (y : L)
    (hyK : (y : G) ∈ K) : crd K J' y = ((hL.coord hJS y : J') : G) := by
  set j : J' := hL.coord hJS y with hj
  have hJ'K : J' ∈ lcal K := hS hJS
  have hjK : (j : G) ∈ K := (mem_lcal_iff.mp hJ'K).1 j.2
  have hl : (j : G)⁻¹ * y ∈ sSup (S \ {J'}) := by
    have hyL : (j : G)⁻¹ * y ∈ L := mul_mem (inv_mem (hL.le hJS j.2)) y.2
    rw [← hL.coord_eq_one_iff hJS ⟨(j : G)⁻¹ * y, hyL⟩]
    have : (⟨(j : G)⁻¹ * y, hyL⟩ : L) = ⟨(j : G)⁻¹, inv_mem (hL.le hJS j.2)⟩ * y := rfl
    rw [this, map_mul]
    have h1 : hL.coord hJS ⟨(j : G)⁻¹, inv_mem (hL.le hJS j.2)⟩ = j⁻¹ :=
      Subtype.ext (hL.coord_of_mem hJS (inv_mem j.2))
    rw [h1, ← hj, inv_mul_cancel]
  have hl' : (j : G)⁻¹ * y ∈ sSup (lcal K \ {J'}) :=
    sSup_le_sSup (Set.sdiff_subset_sdiff_left hS) hl
  have hlK : (j : G)⁻¹ * y ∈ K := mul_mem (inv_mem hjK) hyK
  have h2 : crd K J' ((j : G)⁻¹ * y) = 1 := (crd_eq_one_iff hK hJ'K hlK).mpr hl'
  have h3 : (y : G) = (j : G) * ((j : G)⁻¹ * y) := by group
  calc crd K J' y = crd K J' ((j : G) * ((j : G)⁻¹ * y)) := by rw [← h3]
    _ = crd K J' j * crd K J' ((j : G)⁻¹ * y) := crd_mul hK hJ'K hjK hlK
    _ = j := by rw [h2, mul_one, crd_of_mem hK hJ'K j.2]

theorem exists_norm_elt {p : ℕ} (hp : p.Prime) (hK : IsSemisimple K) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbp : b ^ p = 1) (hJ : J ∈ lcal K)
    (hbJ : b ∉ Subgroup.normalizer (J : Set G)) {x : G} (hx : x ∈ J) :
    ∃ z ∈ perfRes (cenIn K {b}), z ∈ K ∧ crd K J z = x ∧
      (∀ J'' ∈ lcal K, (∀ a ∈ Subgroup.zpowers b, J'' ≠ J.map (MulAut.conj a).toMonoidHom) →
        crd K J'' z = 1) ∧
      (∀ a ∈ Subgroup.zpowers b, crd K (J.map (MulAut.conj a).toMonoidHom) z = a * x * a⁻¹) := by
  classical
  obtain ⟨hJK, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
  set A₀ : Subgroup G := Subgroup.zpowers b with hA₀
  have hAY : A₀ ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hb
  set S : Set (Subgroup G) := {K' | ∃ a ∈ A₀, K' = J.map (MulAut.conj a).toMonoidHom} with hS
  have hL : IsDirectProduct S (orbitClosure J A₀) := isDirectProduct_orbit hAY hJ
  have hAS : ∀ a ∈ A₀, ∀ K' ∈ S, K'.map (MulAut.conj a).toMonoidHom ∈ S := by
    rintro a ha _ ⟨a', ha', rfl⟩
    refine ⟨a * a', mul_mem ha ha', ?_⟩
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [mul_assoc]
  have hJS : J ∈ S := ⟨1, one_mem A₀, by ext y; simp⟩
  have htrans : ∀ K' ∈ S, ∃ a ∈ A₀, K' = J.map (MulAut.conj a).toMonoidHom := fun K' hK' => hK'
  have hSsub : S ⊆ lcal K := by
    rintro _ ⟨a, ha, rfl⟩
    exact map_conj_mem_lcal hJ (hAY ha)
  set L : Subgroup G := orbitClosure J A₀ with hLdef
  have hLK : L ≤ K := by
    refine orbitClosure_le fun a ha => ?_
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hAY ha) y).mp (hJK hy)
    simpa using this
  set C : Subgroup G := L ⊓ Subgroup.centralizer (A₀ : Set G) with hC
  have hAN : A₀ ⊓ Subgroup.normalizer (J : Set G) = ⊥ := zpowers_inf_normalizer_eq_bot hp hbp hbJ
  have hproj : projIn S J C = J := by
    have := projIn_centralizer_eq hL hAS hJS
    rw [hAN] at this
    rw [hC, this]
    refine le_antisymm inf_le_left (le_inf le_rfl fun g _ => ?_)
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    subst hh
    simp
  have hnc' : ∃ a b : J, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hJnc (isMulCommutative_iff.mpr h)
  have hJperf : Group.IsPerfect ↥J := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').1.1
  set ρ : ↥C →* ↥J := (hL.coord hJS).comp (Subgroup.inclusion (inf_le_left : C ≤ L)) with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : G) ∈ sSup (S \ {J}) :=
      (hL.coord_eq_one_iff hJS (Subgroup.inclusion (inf_le_left : C ≤ L) y)).mp hy
    have h2 : (y : G) ∈ L ⊓ Subgroup.centralizer (A₀ : Set G) ⊓ sSup (S \ {J}) :=
      Subgroup.mem_inf.mpr ⟨y.2, h1⟩
    rw [inf_centralizer_inf_sSup_eq_bot_of_transitive hL hAS hJS htrans,
      Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hρsurj : Function.Surjective ρ := by
    intro j
    have hj : (j : G) ∈ projIn S J C := by rw [hproj]; exact j.2
    obtain ⟨y, hyC, hyj⟩ := (hL.mem_projIn_iff hJS).mp hj
    exact ⟨⟨y, hyC⟩, Subtype.ext hyj⟩
  have : Group.IsPerfect ↥J := hJperf
  let e : ↥C ≃* ↥J := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hCperf : Group.IsPerfect ↥C :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hCcen : C ≤ cenIn K {b} := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hLK hz.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hz.2 b (Subgroup.mem_zpowers b)).symm
  have hCle : C ≤ perfRes (cenIn K {b}) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect hCperf hCcen
  have hxproj : x ∈ projIn S J C := by rw [hproj]; exact hx
  obtain ⟨y, hyC, hyx⟩ := (hL.mem_projIn_iff hJS).mp hxproj
  have hzK : (y : G) ∈ K := hLK y.2
  have hzx : crd K J y = x := by
    rw [crd_eq_coord_of_mem hK hL hSsub hJS y hzK]
    exact hyx
  refine ⟨y, hCle hyC, hzK, hzx, fun J'' hJ'' hne => ?_, fun a ha => ?_⟩
  · have hJ''S : J'' ∉ S := fun ⟨a, ha, h⟩ => hne a ha h
    have hzsS : (y : G) ∈ sSup S := by rw [hL.sSup_eq]; exact y.2
    have hle : sSup S ≤ sSup (lcal K \ {J''}) :=
      sSup_le_sSup fun K' hK' => ⟨hSsub hK', fun h => hJ''S (Set.mem_singleton_iff.mp h ▸ hK')⟩
    exact (crd_eq_one_iff hK hJ'' hzK).mpr (hle hzsS)
  · have hcomm : a * (y : G) * a⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.mp hyC.2 a ha
      rw [this, mul_inv_cancel_right]
    have := crd_conj hK hJ (hAY ha) hzK
    rw [hcomm, hzx] at this
    exact this

end Norm


section Blocks

variable {K : Subgroup G}

omit [Finite G] in
theorem mem_sSup_diff_of_mem {S T : Set (Subgroup G)} {K' : Subgroup G}
    (hK : IsDirectProduct S K') (hT : T ⊆ S) {J : Subgroup G} (hJT : J ∈ T) {x : G}
    (hxT : x ∈ sSup T) (hxJ : x ∈ sSup (S \ {J})) : x ∈ sSup (T \ {J}) := by
  have hJS : J ∈ S := hT hJT
  have hTeq : T = insert J (T \ {J}) := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hJT]
  rw [hTeq, sSup_insert] at hxT
  have hle : sSup (T \ {J}) ≤ sSup (S \ {J}) := sSup_le_sSup (Set.sdiff_subset_sdiff_left hT)
  obtain ⟨j, hj, t, ht, rfl⟩ := (mem_sup_iff_of_commute fun u hu v hv =>
    hK.commute_sSup_diff hJS u hu v (hle hv)).mp hxT
  have hjS : j ∈ sSup (S \ {J}) := by
    have := mul_mem hxJ (inv_mem (hle ht))
    simpa using this
  have hjbot : j ∈ J ⊓ sSup (S \ {J}) := ⟨hj, hjS⟩
  rw [disjoint_iff.mp (hK.indep hJS), Subgroup.mem_bot] at hjbot
  rw [hjbot, one_mul]
  exact ht

theorem crd_eq_one_of_block (hK : IsSemisimple K) {N : Subgroup G} (hNK : N ≤ K)
    {P : Set (Set (Subgroup G))} (hunion : ⋃₀ P = lcal K) (hdisj : P.PairwiseDisjoint id)
    (hdp : IsDirectProduct ((fun T => N ⊓ sSup T) '' P) N)
    (hdiag : ∀ T ∈ P, IsDiagonal T (N ⊓ sSup T)) {T : Set (Subgroup G)} (hT : T ∈ P)
    {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ T) (hJ₂ : J₂ ∈ T) {z : G} (hz : z ∈ N)
    (h1 : crd K J₁ z = 1) : crd K J₂ z = 1 := by
  have hTsub : T ⊆ lcal K := fun J hJ => hunion ▸ ⟨T, hT, hJ⟩
  have hX : (N ⊓ sSup T) ∈ (fun T => N ⊓ sSup T) '' P := ⟨T, hT, rfl⟩
  have hpair := hdp.isDirectPair hX
  set Y : Subgroup G := sSup ((fun T => N ⊓ sSup T) '' P \ {N ⊓ sSup T}) with hY
  have hzNY : z ∈ (N ⊓ sSup T) ⊔ Y := by rw [hpair.sup_eq]; exact hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_commute hpair.commute).mp hzNY
  have hxN : x ∈ N := hx.1
  have hyN : y ∈ N := by
    have : Y ≤ N := le_sup_right.trans hpair.sup_eq.le
    exact this hy
  have hxK : x ∈ K := hNK hxN
  have hyK : y ∈ K := hNK hyN
  have hYle : ∀ J ∈ T, y ∈ sSup (lcal K \ {J}) := by
    intro J hJ
    have : Y ≤ sSup (lcal K \ {J}) := by
      refine sSup_le fun X' hX' => ?_
      obtain ⟨⟨T', hT', rfl⟩, hne⟩ := hX'
      have hTT' : T ≠ T' := fun h => hne (by rw [h]; rfl)
      have hdis : Disjoint T T' := hdisj hT hT' hTT'
      have hJT' : J ∉ T' := fun h => Set.disjoint_left.mp hdis hJ h
      refine inf_le_right.trans (sSup_le_sSup fun J' hJ' => ⟨hunion ▸ ⟨T', hT', hJ'⟩, ?_⟩)
      intro h
      exact hJT' (Set.mem_singleton_iff.mp h ▸ hJ')
    exact this hy
  have hcy : ∀ J ∈ T, crd K J y = 1 := fun J hJ =>
    (crd_eq_one_iff hK (hTsub hJ) hyK).mpr (hYle J hJ)
  have hx1 : crd K J₁ x = 1 := by
    have := crd_mul hK (hTsub hJ₁) hxK hyK
    rw [h1, hcy J₁ hJ₁, mul_one] at this
    exact this.symm
  have hxT : x ∈ sSup T := hx.2
  have hxS : x ∈ sSup (lcal K \ {J₁}) := (crd_eq_one_iff hK (hTsub hJ₁) hxK).mp hx1
  have hxTd : x ∈ sSup (T \ {J₁}) :=
    mem_sSup_diff_of_mem hK.isDirectProduct_lcal hTsub hJ₁ hxT hxS
  have hxbot : x ∈ (N ⊓ sSup T) ⊓ sSup (T \ {J₁}) := ⟨hx, hxTd⟩
  rw [((hdiag T hT).2 J₁ hJ₁).1, Subgroup.mem_bot] at hxbot
  rw [hxbot, one_mul]
  exact hcy J₂ hJ₂

end Blocks


section Elementary

omit [Finite G] in
theorem commute_of_mem_comm {A : Subgroup G} (hA : IsMulCommutative A) {g a : G} (hg : g ∈ A)
    (ha : a ∈ A) : Commute g a :=
  congrArg Subtype.val (hA.is_comm.comm (⟨g, hg⟩ : A) ⟨a, ha⟩)

omit [Finite G] in
theorem card_zpowers_of_pow_eq_one {p : ℕ} (hp : p.Prime) {b : G} (hbp : b ^ p = 1)
    (hb1 : b ≠ 1) : Nat.card (Subgroup.zpowers b) = p := by
  have := Fact.mk hp
  rw [Nat.card_zpowers, orderOf_eq_prime hbp hb1]

theorem mem_zpowers_of_mem_zpowers {p : ℕ} (hp : p.Prime) {b c : G} (hbp : b ^ p = 1)
    (hcp : c ^ p = 1) (hb1 : b ≠ 1) (h : b ∈ Subgroup.zpowers c) : c ∈ Subgroup.zpowers b := by
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h
    exact hb1 h
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr h
  have hcard : Nat.card (Subgroup.zpowers c) ≤ Nat.card (Subgroup.zpowers b) := by
    rw [card_zpowers_of_pow_eq_one hp hbp hb1, card_zpowers_of_pow_eq_one hp hcp hc1]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ Subgroup.mem_zpowers c

theorem exists_complement_gen {p : ℕ} (hp : p.Prime) {B Bj : Subgroup G} (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2) (hBj : Bj ≤ B) (hBjc : Nat.card Bj ≤ p) {b : G} (hbB : b ∈ B)
    (hbBj : b ∉ Bj) :
    ∃ c ∈ B, c ≠ 1 ∧ c ∉ Subgroup.zpowers b ∧ Bj ≤ Subgroup.zpowers c := by
  have hbp : b ^ p = 1 := hB.2 b hbB
  have hb1 : b ≠ 1 := fun h => hbBj (h ▸ one_mem _)
  have hcb : Nat.card (Subgroup.zpowers b) = p := card_zpowers_of_pow_eq_one hp hbp hb1
  by_cases hbot : Bj = ⊥
  · have : ∃ c ∈ B, c ∉ Subgroup.zpowers b := by
      by_contra hcon
      push Not at hcon
      have hle : B ≤ Subgroup.zpowers b := fun c hc => hcon c hc
      have := Subgroup.card_le_of_le hle
      rw [hcb, hBc] at this
      have h2 : p ^ 2 ≤ p := this
      have : 1 < p := hp.one_lt
      nlinarith
    obtain ⟨c, hcB, hc⟩ := this
    exact ⟨c, hcB, fun h => hc (h ▸ one_mem _), hc, hbot ▸ bot_le⟩
  · obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hbot)
    have hcBj : (c : G) ∈ Bj := c.2
    have hcB : (c : G) ∈ B := hBj hcBj
    have hc1' : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hcp : (c : G) ^ p = 1 := hB.2 c hcB
    have hcle : Subgroup.zpowers (c : G) ≤ Bj := Subgroup.zpowers_le.mpr hcBj
    have hcc : Nat.card (Subgroup.zpowers (c : G)) = p := card_zpowers_of_pow_eq_one hp hcp hc1'
    have heq : Subgroup.zpowers (c : G) = Bj :=
      Subgroup.eq_of_le_of_card_ge hcle (by rw [hcc]; exact hBjc)
    refine ⟨c, hcB, hc1', fun h => hbBj ?_, heq.ge⟩
    have := mem_zpowers_of_mem_zpowers hp hcp hbp hc1' h
    rw [heq] at this
    exact this

end Elementary


section Main

variable {K N B : Subgroup G}

structure IsBlocks (K N : Subgroup G) (P : Set (Set (Subgroup G))) : Prop where
  le : N ≤ K
  union : ⋃₀ P = lcal K
  disj : P.PairwiseDisjoint id
  dp : IsDirectProduct ((fun T => N ⊓ sSup T) '' P) N
  diag : ∀ T ∈ P, IsDiagonal T (N ⊓ sSup T)

theorem exists_isBlocks (hK : IsSemisimple K) (hNK : N ≤ K)
    (hproj : ∀ J ∈ lcal K, projIn (lcal K) J N = J) : ∃ P, IsBlocks K N P := by
  obtain ⟨P, -, hunion, hdisj, hdp, hdiag⟩ := exists_partition_isDiagonal hK hNK hproj
  exact ⟨P, ⟨hNK, hunion, hdisj, hdp, hdiag⟩⟩

omit [Finite G] in
theorem projIn_singleton_le (J X : Subgroup G) : projIn ({J} : Set (Subgroup G)) J X ≤ X := by
  unfold projIn proj
  refine (Subgroup.closure_le X).mpr ?_
  rintro j ⟨-, l, hl, hjl⟩
  have : l ∈ (⊥ : Subgroup G) := by
    have h : sSup (({J} : Set (Subgroup G)) \ {J}) = ⊥ := by simp
    rwa [h] at hl
  rw [Subgroup.mem_bot] at this
  subst this
  simpa using hjl


theorem inf_ne_bot_of_caseB {p : ℕ} (hp : p.Prime) (hK : IsSemisimple K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2)
    (hfaith : ∀ J ∈ lcal K, ∀ E : Subgroup G, E ≤ B → E ≤ Subgroup.normalizer (J : Set G) →
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ → Nat.card E ≤ p)
    (hN : ∀ b ∈ B, b ≠ 1 → perfRes (cenIn K {b}) ≤ N) {P : Set (Set (Subgroup G))}
    (hP : IsBlocks K N P) {J : Subgroup G} (hJ : J ∈ lcal K)
    (hcase : ∀ b ∈ B, b ≠ 1 → b ∉ Subgroup.centralizer (J : Set G)) : N ⊓ J ≠ ⊥ := by
  classical
  obtain ⟨hJK, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
  have hJne : J ≠ ⊥ := by
    rintro rfl
    exact hJnc inferInstance
  obtain ⟨T, hT, hJT⟩ : ∃ T ∈ P, J ∈ T := by
    have : J ∈ ⋃₀ P := hP.union ▸ hJ
    obtain ⟨T, hT, hJT⟩ := this
    exact ⟨T, hT, hJT⟩
  suffices hTJ : T = {J} by
    have hd := ((hP.diag T hT).2 J hJT).2
    subst hTJ
    rw [sSup_singleton] at hd
    have hle : J ≤ N ⊓ J := by
      calc J = projIn {J} J (N ⊓ J) := hd.symm
        _ ≤ N ⊓ J := projIn_singleton_le J (N ⊓ J)
    intro hbot
    rw [hbot] at hle
    exact hJne (le_bot_iff.mp hle)
  by_contra hTne
  obtain ⟨J', hJ'T, hJ'J⟩ : ∃ J' ∈ T, J' ≠ J := by
    by_contra hcon
    push Not at hcon
    exact hTne (Set.eq_singleton_iff_unique_mem.mpr ⟨hJT, fun J' hJ' => hcon J' hJ'⟩)
  have hJ'K : J' ∈ lcal K := hP.union ▸ ⟨T, hT, hJ'T⟩
  set Bj : Subgroup G := B ⊓ Subgroup.normalizer (J : Set G) with hBj
  have hBjc : Nat.card Bj ≤ p := by
    refine hfaith J hJ Bj inf_le_left inf_le_right ?_
    rw [eq_bot_iff]
    rintro g ⟨⟨hgB, hgN⟩, hgC⟩
    rw [Subgroup.mem_bot]
    by_contra hne
    exact hcase g hgB hne hgC
  obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (J : Set G) := by
    by_contra hcon
    push Not at hcon
    have : Bj = B := inf_eq_left.mpr fun b hb => hcon b hb
    rw [this, hBc] at hBjc
    have h1 : 1 < p := hp.one_lt
    nlinarith
  have hbp : b ^ p = 1 := hB.2 b hbB
  have hb1 : b ≠ 1 := fun h => hbN (h ▸ one_mem _)
  obtain ⟨c, hcB, hc1, hcb, hBjc'⟩ :=
    exists_complement_gen hp hB hBc inf_le_left hBjc hbB (fun h => hbN h.2)
  have hcp : c ^ p = 1 := hB.2 c hcB
  have hbcB : b * c ∈ B := mul_mem hbB hcB
  have hbcp : (b * c) ^ p = 1 := hB.2 _ hbcB
  have hcomm : Commute b c := commute_of_mem_comm hB.1 hbB hcB
  have hbcN : b * c ∉ Subgroup.normalizer (J : Set G) := by
    intro h
    have hmem : b * c ∈ Subgroup.zpowers c := hBjc' ⟨hbcB, h⟩
    have hbc : b ∈ Subgroup.zpowers c := by
      have := mul_mem hmem (inv_mem (Subgroup.mem_zpowers c))
      simpa using this
    exact hcb (mem_zpowers_of_mem_zpowers hp hbp hcp hb1 hbc)
  have hbc1 : b * c ≠ 1 := fun h => hbcN (h ▸ one_mem _)
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := hBK hbB
  have hbcK : b * c ∈ Subgroup.normalizer (K : Set G) := hBK hbcB
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ J, x ≠ 1 := by
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJne
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have key : ∀ b' ∈ B, b' ∉ Subgroup.normalizer (J : Set G) → b' ≠ 1 → b' ^ p = 1 →
      ∃ a ∈ Subgroup.zpowers b', J' = J.map (MulAut.conj a).toMonoidHom := by
    intro b' hb'B hb'N hb'1 hb'p
    by_contra hcon
    push Not at hcon
    obtain ⟨z, hzP, hzK, hzJ, hz3, -⟩ := exists_norm_elt hp hK (hBK hb'B) hb'p hJ hb'N hx₀
    have hz1 : crd K J' z = 1 := hz3 J' hJ'K hcon
    have hzN : z ∈ N := hN b' hb'B hb'1 hzP
    have := crd_eq_one_of_block hK hP.le hP.union hP.disj hP.dp hP.diag hT hJ'T hJT hzN hz1
    rw [hzJ] at this
    exact hx₀1 this
  obtain ⟨a₁, ha₁, hJ'a₁⟩ := key b hbB hbN hb1 hbp
  obtain ⟨a₂, ha₂, hJ'a₂⟩ := key (b * c) hbcB hbcN hbc1 hbcp
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₂
  have hgB : (b ^ k)⁻¹ * (b * c) ^ m ∈ B := mul_mem (inv_mem (zpow_mem hbB k)) (zpow_mem hbcB m)
  have hgC : (b ^ k)⁻¹ * (b * c) ^ m ∈ Subgroup.centralizer (J : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨z₁, hz₁P, hz₁K, hz₁J, -, hz₁c⟩ := exists_norm_elt hp hK hbK hbp hJ hbN hx
    obtain ⟨z₂, hz₂P, hz₂K, hz₂J, -, hz₂c⟩ := exists_norm_elt hp hK hbcK hbcp hJ hbcN hx
    have e₁ := hz₁c (b ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    have e₂ := hz₂c ((b * c) ^ m) (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
    rw [← hJ'a₁] at e₁
    rw [← hJ'a₂] at e₂
    have hu : z₁ * z₂⁻¹ ∈ N :=
      mul_mem (hN b hbB hb1 hz₁P) (inv_mem (hN (b * c) hbcB hbc1 hz₂P))
    have hc1' : crd K J (z₁ * z₂⁻¹) = 1 := by
      rw [crd_mul hK hJ hz₁K (inv_mem hz₂K), crd_inv hK hJ hz₂K, hz₁J, hz₂J, mul_inv_cancel]
    have hc2 := crd_eq_one_of_block hK hP.le hP.union hP.disj hP.dp hP.diag hT hJT hJ'T hu hc1'
    rw [crd_mul hK hJ'K hz₁K (inv_mem hz₂K), crd_inv hK hJ'K hz₂K, e₁, e₂, mul_inv_eq_one] at hc2
    calc x * ((b ^ k)⁻¹ * (b * c) ^ m)
        = (b ^ k)⁻¹ * (b ^ k * x * (b ^ k)⁻¹) * (b * c) ^ m := by group
      _ = (b ^ k)⁻¹ * ((b * c) ^ m * x * ((b * c) ^ m)⁻¹) * (b * c) ^ m := by rw [hc2]
      _ = (b ^ k)⁻¹ * (b * c) ^ m * x := by group
  have hg1 : (b ^ k)⁻¹ * (b * c) ^ m = 1 := by
    by_contra hne
    exact hcase _ hgB hne hgC
  have hbk : b ^ k = b ^ m * c ^ m := by
    rw [← hcomm.mul_zpow m]
    exact inv_mul_eq_one.mp hg1
  have hm : (p : ℤ) ∣ m := by
    by_contra hm
    have hcm : c ^ m ∈ Subgroup.zpowers b := by
      have : c ^ m = (b ^ m)⁻¹ * b ^ k := by rw [hbk]; group
      rw [this]
      exact mul_mem (inv_mem (Subgroup.zpow_mem_zpowers b m)) (Subgroup.zpow_mem_zpowers b k)
    exact hcb (mem_of_zpow_mem hp hcp hm hcm)
  obtain ⟨m', rfl⟩ := hm
  have hbm : b ^ ((p : ℤ) * m') = 1 := by rw [zpow_mul, zpow_natCast, hbp, one_zpow]
  have hcm : c ^ ((p : ℤ) * m') = 1 := by rw [zpow_mul, zpow_natCast, hcp, one_zpow]
  rw [hbm, hcm, mul_one] at hbk
  rw [hbk] at hJ'a₁
  apply hJ'J
  rw [hJ'a₁]
  ext y
  simp


omit [Finite G] in
theorem exists_not_mem_normalizer {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hBc : Nat.card B = p ^ 2)
    (hfaith' : Nat.card (B ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) ≤ p) :
    ∃ b ∈ B, b ∉ Subgroup.normalizer (J : Set G) := by
  by_contra hcon
  push Not at hcon
  have : (B ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) = B :=
    inf_eq_left.mpr fun b hb => hcon b hb
  rw [this, hBc] at hfaith'
  have h1 : 1 < p := hp.one_lt
  nlinarith

theorem le_iSup_perfRes_cenIn {p : ℕ} (hp : p.Prime) (hK : IsSemisimple K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2)
    (hfaith : ∀ J ∈ lcal K, ∀ E : Subgroup G, E ≤ B → E ≤ Subgroup.normalizer (J : Set G) →
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ → Nat.card E ≤ p) :
    K ≤ ⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn K {b}) := by
  classical
  set N : Subgroup G := ⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn K {b}) with hN
  have hNb : ∀ b ∈ B, b ≠ 1 → perfRes (cenIn K {b}) ≤ N := fun b hb hb1 =>
    le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => perfRes (cenIn K {b})) hb1)
  have hNK : N ≤ K := iSup₂_le fun b _ => iSup_le fun _ =>
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hcaseA : ∀ J ∈ lcal K, (∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (J : Set G)) →
      J ≤ N := by
    intro J hJ ⟨b, hbB, hb1, hbC⟩
    obtain ⟨hJK, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
    have hnc' : ∃ a b : J, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hJnc (isMulCommutative_iff.mpr h)
    have hJperf : Group.IsPerfect ↥J := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').1.1
    have hJc : J ≤ cenIn K {b} := fun y hy =>
      Subgroup.mem_inf.mpr ⟨hJK hy, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hbC y hy)⟩
    exact (CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect hJperf
      hJc).trans (hNb b hbB hb1)
  have hJne : ∀ J ∈ lcal K, J ≠ ⊥ := by
    intro J hJ hbot
    obtain ⟨-, -, -, hJnc⟩ := mem_lcal_iff.mp hJ
    rw [hbot] at hJnc
    exact hJnc inferInstance
  have hproj : ∀ J ∈ lcal K, projIn (lcal K) J N = J := by
    intro J hJ
    apply le_antisymm (projIn_le J N)
    intro x hx
    rw [mem_projIn_iff_crd hK hJ]
    have hJK : J ≤ K := (mem_lcal_iff.mp hJ).1
    by_cases hA : ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (J : Set G)
    · exact ⟨x, hJK hx, hcaseA J hJ hA hx, crd_of_mem hK hJ hx⟩
    · push Not at hA
      have hcard : Nat.card (B ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) ≤ p := by
        refine hfaith J hJ _ inf_le_left inf_le_right ?_
        rw [eq_bot_iff]
        rintro g ⟨⟨hgB, -⟩, hgC⟩
        rw [Subgroup.mem_bot]
        by_contra hne
        exact hA g hgB hne hgC
      obtain ⟨b, hbB, hbN⟩ := exists_not_mem_normalizer hp hBc hcard
      have hb1 : b ≠ 1 := fun h => hbN (h ▸ one_mem _)
      obtain ⟨z, hzP, hzK, hzJ, -, -⟩ :=
        exists_norm_elt hp hK (hBK hbB) (hB.2 b hbB) hJ hbN hx
      exact ⟨z, hzK, hNb b hbB hb1 hzP, hzJ⟩
  obtain ⟨P, hP⟩ := exists_isBlocks hK hNK hproj
  have hint : ∀ J ∈ lcal K, N ⊓ J ≠ ⊥ := by
    intro J hJ
    by_cases hA : ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (J : Set G)
    · rw [inf_eq_right.mpr (hcaseA J hJ hA)]
      exact hJne J hJ
    · push Not at hA
      exact inf_ne_bot_of_caseB hp hK hBK hB hBc hfaith hNb hP hJ hA
  exact (eq_of_projIn_eq_of_inf_ne_bot hK hNK hproj hint).ge

end Main

end Sec6Gen

end CFSG.SignalizerFunctorTheorem.McBride.Near
