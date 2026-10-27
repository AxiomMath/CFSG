module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairGen
public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairDih
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.GroupTheory.PCoreSurjective
import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz Bar2)

private lemma w183b2_isPGroup_of_normal_isPGroup_quotient {G : Type*} [Group G] {N : Subgroup G}
    [N.Normal] {p : ℕ} (hN : IsPGroup p N) (hq : IsPGroup p (G ⧸ N)) : IsPGroup p G := by
  have htop : IsPGroup p (⊤ : Subgroup (G ⧸ N)) := hq.of_equiv Subgroup.topEquiv.symm
  have hker : IsPGroup p (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; exact hN
  have h := htop.comap_of_ker_isPGroup (QuotientGroup.mk' N) hker
  rw [Subgroup.comap_top] at h
  exact h.of_equiv Subgroup.topEquiv

private lemma w183b2_le_pCore_of_normal_isPGroup {G : Type*} [Group G] {p : ℕ}
    {N : Subgroup G} (hN : N.Normal) (hp : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup (show N ∈ {K : Subgroup G | K.Normal ∧ IsPGroup p K} from ⟨hN, hp⟩)

private lemma w183b2_orderOf_eq_two_of_card_eq_two {Lb : Type*} [Group Lb] {P : Subgroup Lb}
    (hP : Nat.card P = 2) {a : Lb} (ha : a ∈ P) (ha1 : a ≠ 1) : orderOf a = 2 := by
  have hdvd : orderOf a ∣ 2 := by
    have h := orderOf_dvd_natCard (⟨a, ha⟩ : P)
    rw [Subgroup.orderOf_mk, hP] at h
    exact h
  have hne : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private lemma w183b2_exists_ne_one_of_card_two {G : Type} [Group G] [Finite G]
    (h : Nat.card G = 2) : ∃ x : G, x ≠ 1 := by
  haveI : Fintype G := Fintype.ofFinite G
  have h2 : Fintype.card G = 2 := by rwa [← Nat.card_eq_fintype_card]
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact exists_ne (1 : G)

private lemma w183b2_four_le_pow_two {k : ℕ} (hk : 2 ≤ k) : 4 ≤ 2 ^ k := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

private lemma w183b2_eight_le_pow_mul {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁ ∧ k₁ ≤ 2)
    (hk₂ : 1 ≤ k₂ ∧ k₂ ≤ 2) (hne : ¬ (k₁ = 1 ∧ k₂ = 1)) : 8 ≤ 2 ^ k₁ * 2 ^ k₂ := by
  rw [← pow_add]
  have hsum : 3 ≤ k₁ + k₂ := by omega
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (k₁ + k₂) := Nat.pow_le_pow_right (by norm_num) hsum

private lemma w183b2_two_mul_orderOf_dvd {Lb : Type} [Group Lb] [Finite Lb] {a b : Lb}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a ≠ b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    2 * orderOf (a * b) ∣ Nat.card Lb := by
  obtain ⟨e⟩ := w183b2_dihedral_of_involutions ha hb hab ha1 hb1
  have hcard : Nat.card (Subgroup.closure ({a, b} : Set Lb)) = 2 * orderOf (a * b) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

private lemma w183b2_odd_of_card {Lb : Type} [Group Lb] [Finite Lb] {a b : Lb}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a ≠ b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    {n : ℕ} (hodd : Odd n) (hcard : Nat.card Lb = 2 * n) : Odd (orderOf (a * b)) := by
  have hdvd := w183b2_two_mul_orderOf_dvd ha hb hab ha1 hb1
  rw [hcard] at hdvd
  exact hodd.of_dvd_nat ((Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)).mp hdvd)

private lemma w183b2_pairabs_odd_dihedral {Lb : Type} [Group Lb] [Finite Lb]
    {m : ℕ} (hm : Odd m) (e : Lb ≃* DihedralGroup m) (P₁ P₂ : Subgroup Lb)
    (hP₁ : Nat.card P₁ = 2) (hP₂ : Nat.card P₂ = 2) (hP : P₁ ≠ P₂) {a b : Lb}
    (ha : a ∈ P₁) (ha1 : a ≠ 1) (hb : b ∈ P₂) (hb1 : b ≠ 1) : Odd (orderOf (a * b)) := by
  have hcard : Nat.card Lb = 2 * m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hza : Subgroup.zpowers a = P₁ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha)
      (by rw [hP₁, Nat.card_zpowers, w183b2_orderOf_eq_two_of_card_eq_two hP₁ ha ha1])
  have hzb : Subgroup.zpowers b = P₂ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
      (by rw [hP₂, Nat.card_zpowers, w183b2_orderOf_eq_two_of_card_eq_two hP₂ hb hb1])
  have hab : a ≠ b := by
    intro h
    exact hP (by rw [← hza, ← hzb, h])
  have ha2 : a * a = 1 := by
    have h2 := w183b2_orderOf_eq_two_of_card_eq_two hP₁ ha ha1
    have := pow_orderOf_eq_one a
    rw [h2] at this
    simpa [pow_two] using this
  have hb2 : b * b = 1 := by
    have h2 := w183b2_orderOf_eq_two_of_card_eq_two hP₂ hb hb1
    have := pow_orderOf_eq_one b
    rw [h2] at this
    simpa [pow_two] using this
  exact w183b2_odd_of_card ha2 hb2 hab ha1 hb1 hm hcard

private lemma w183b2_isL2_ne_one {Lb : Type} [Group Lb] {d : ℕ} (h : IsL2 Lb d) : d ≠ 1 := by
  intro hd
  have hadm := h.admissible
  rw [hd] at hadm
  exact hadm.2.2.2.1 (Prod.ext rfl (by norm_num : (2 : ℕ) ^ 1 = 2))

private lemma w183b2_isSz_three_le {Lb : Type} [Group Lb] {d : ℕ} (h : IsSz Lb d) : 3 ≤ d :=
  h.admissible.2.2.2.2.2

private lemma w183b2_dihedral_d_eq_one {Lb : Type} [Group Lb] [Finite Lb] {m d : ℕ}
    (hm : Odd m) (e : Lb ≃* DihedralGroup m) (P : Subgroup Lb) (hd1 : 1 ≤ d)
    (hc : Nat.card P = 2 ^ d) : d = 1 := by
  have hcard : Nat.card Lb = 2 * m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hdvd : 2 ^ d ∣ 2 * m := by
    rw [← hc, ← hcard]
    exact Subgroup.card_subgroup_dvd_card P
  have hcop : Nat.Coprime (2 ^ d) m := (Nat.coprime_two_right.mpr hm).symm.pow_left d
  have h2dvd : 2 ^ d ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have hle : 2 ^ d ≤ 2 := Nat.le_of_dvd (by norm_num) h2dvd
  have hle' : 2 ^ d ≤ 2 ^ 1 := by simpa using hle
  have : d ≤ 1 := (Nat.pow_le_pow_iff_right (show 1 < (2 : ℕ) by norm_num)).mp hle'
  omega

private theorem w183b2_pCore_eq_of_simple_quotient {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN2 : IsPGroup 2 N)
    {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] (hQ2 : ¬ IsPGroup 2 Q)
    (e : X ⧸ N ≃* Q) : CFSG.pCore 2 X = N := by
  refine le_antisymm ?_ (w183b2_le_pCore_of_normal_isPGroup (inferInstance : N.Normal) hN2)
  have hQ : CFSG.pCore 2 Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 Q) with h | h
    · exact h
    · have htop : IsPGroup 2 (⊤ : Subgroup Q) := by
        have := CFSG.pCore_isPGroup (p := 2) (G := Q)
        rwa [h] at this
      exact absurd (htop.of_equiv Subgroup.topEquiv) hQ2
  have hmap := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN2)
  have hmap' : CFSG.pCore 2 (X ⧸ N) = ⊥ := by
    have h := CFSG.pCore_map_iso 2 e
    rw [hQ, Subgroup.map_eq_bot_iff] at h
    exact le_bot_iff.mp (h.trans (le_of_eq ((e.toMonoidHom).ker_eq_bot e.injective)))
  rw [hmap'] at hmap
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap

private lemma w183b2_isPGroup_of_zpowers_involution {G : Type} [Group G] [Finite G] {x : G}
    (hx : x * x = 1) (hG : Subgroup.zpowers x = ⊤) : IsPGroup 2 G := by
  have hcard : Nat.card G = orderOf x := by
    rw [← Nat.card_congr Subgroup.topEquiv.toEquiv, ← hG, Nat.card_zpowers]
  have hdvd : orderOf x ∣ 2 := by
    rw [← pow_two] at hx
    exact orderOf_dvd_iff_pow_eq_one.mpr hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [hcard, h]; norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [hcard, h]; norm_num)

theorem w183b2_pair_abs_isSz_excluded
    {Xh Lb Y : Type} [Group Xh] [Finite Xh] [Group Lb] [Finite Lb] [Group Y] [Finite Y]
    (π : Xh →* Lb) (hK : IsPGroup 2 π.ker) (ψ : Xh →* Y) (hC : IsSolvable ψ.ker)
    (h13 : ¬ 13 ∣ Nat.card Y) (h : IsSz Lb 3) (hπ : π.range = ⊤) : False := by
  obtain ⟨-, hsz⟩ := CFSG.Blueprint.LieModel.suzukiModel h
  obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := hsz
  have ha1 : a = 1 := by omega
  subst ha1
  have hF' : Nat.card F = 2 ^ (2 * 1 + 1) := by rw [hF, hf]
  have hcard : Nat.card Lb = 29120 := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF']
    norm_num
  haveI hsimple : IsSimpleGroup Lb := by
    haveI := (CFSG.LieType.Ree.suzuki_simple (K := F) ha hF').2.2
    exact e.isSimpleGroup
  haveI hperf : Group.IsPerfect Lb := by
    haveI := (CFSG.LieType.Ree.suzuki_perfect (K := F) ha hF').2
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Nontrivial Lb := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  have hπsurj : Function.Surjective π := MonoidHom.range_eq_top.mp hπ
  have hψle : ψ.ker ≤ π.ker := by
    haveI : IsSolvable ψ.ker := hC
    have hmap_solv : IsSolvable ↥((ψ.ker).map π) := by
      have hrange : (π.comp (ψ.ker).subtype).range = (ψ.ker).map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact @Group.isSolvable_of_surjective ↥ψ.ker
        ↥((π.comp (ψ.ker).subtype).range) _ _
        (π.comp (ψ.ker).subtype).rangeRestrict
        (π.comp (ψ.ker).subtype).rangeRestrict_surjective hC
    have hmap_normal : ((ψ.ker).map π).Normal :=
      (inferInstance : ψ.ker.Normal).map π hπsurj
    haveI := hmap_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ψ.ker).map π) with h | h
    · rw [Subgroup.map_eq_bot_iff] at h; exact h
    · exfalso
      have htop : IsSolvable ↥(⊤ : Subgroup Lb) := by rw [h] at hmap_solv; exact hmap_solv
      have hsolv : IsSolvable Lb :=
        @Group.isSolvable_of_surjective (⊤ : Subgroup Lb) Lb _ _
          (Subgroup.topEquiv : (⊤ : Subgroup Lb) ≃* Lb).toMonoidHom
          Subgroup.topEquiv.surjective htop
      exact Group.IsPerfect.not_isSolvable Lb hsolv
  have h13Lb : 13 ∣ Nat.card Lb := by rw [hcard]; norm_num
  have hXπ : Nat.card Xh = Nat.card (Xh ⧸ π.ker) * Nat.card π.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have hXψ : Nat.card Xh = Nat.card (Xh ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hqπ : Nat.card (Xh ⧸ π.ker) = Nat.card Lb :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).toEquiv
  have hqψ : Nat.card (Xh ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have h13X : 13 ∣ Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← hqψ, ← hXψ, hXπ, hqπ]
    exact Dvd.dvd.mul_right h13Lb _
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 13)).mp h13X with hr | hk
  · exact h13 (hr.trans (Subgroup.card_subgroup_dvd_card ψ.range))
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hK
    have hdvd : Nat.card ψ.ker ∣ 2 ^ n := by
      rw [← hn]; exact Subgroup.card_dvd_of_le hψle
    have h132 : 13 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 13) (hk.trans hdvd))
    omega

theorem w183b2_pair_abs
    (hL28 : FinPairGenL28) (hSz8 : FinPairGenSz8)
    {Xh Lb Y : Type} [Group Xh] [Finite Xh] [Group Lb] [Finite Lb] [Group Y] [Finite Y]
    (π : Xh →* Lb) (hK : IsPGroup 2 π.ker) (ψ : Xh →* Y) (hC : IsSolvable ψ.ker)
    (h13 : ¬ 13 ∣ Nat.card Y) (Ah Bh : Subgroup Xh) (hgen : Ah ⊔ Bh = ⊤) (k₁ k₂ d : ℕ)
    (hk₁ : 1 ≤ k₁ ∧ k₁ ≤ 2) (hk₂ : 1 ≤ k₂ ∧ k₂ ≤ 2) (hd₁ : k₁ ≤ d ∧ d ≤ k₁ + 1)
    (hd₂ : k₂ ≤ d ∧ d ≤ k₂ + 1)
    (hshape : IsL2 Lb d ∨ IsSz Lb d ∨ ∃ m : ℕ, Odd m ∧ Nonempty (Lb ≃* DihedralGroup m))
    (P₁ P₂ : Subgroup Lb) (hP₁ : IsElemAbelian 2 P₁)
    (hP₂ : IsElemAbelian 2 P₂) (hc₁ : Nat.card P₁ = 2 ^ d) (hc₂ : Nat.card P₂ = 2 ^ d)
    (hP : P₁ ≠ P₂) (hAP : Ah.map π ≤ P₁) (hBP : Bh.map π ≤ P₂)
    (hAc : Nat.card (Ah.map π) = 2 ^ k₁) (hBc : Nat.card (Bh.map π) = 2 ^ k₂) :
    PairQuotOK k₁ k₂ ψ.range := by
  by_cases h11 : k₁ = 1 ∧ k₂ = 1
  · obtain ⟨hk1, hk2⟩ := h11
    have hEcard : Nat.card (Ah.map π) = 2 := by rw [hAc, hk1]; norm_num
    have hFcard : Nat.card (Bh.map π) = 2 := by rw [hBc, hk2]; norm_num
    obtain ⟨a', ha'1⟩ := w183b2_exists_ne_one_of_card_two hEcard
    obtain ⟨b', hb'1⟩ := w183b2_exists_ne_one_of_card_two hFcard
    set a : Lb := (a' : Lb) with ha
    set b : Lb := (b' : Lb) with hb
    have haE : a ∈ Ah.map π := a'.2
    have hbF : b ∈ Bh.map π := b'.2
    have ha1 : a ≠ 1 := fun h => ha'1 (Subtype.ext (by simpa [ha] using h))
    have hb1 : b ≠ 1 := fun h => hb'1 (Subtype.ext (by simpa [hb] using h))
    have hodd : Odd (orderOf (a * b)) := by
      rcases hshape with hL2 | hSz | ⟨m, hm, e⟩
      · have hdle : d ≤ 2 := by omega
        have hd2 : d = 2 := by have := w183b2_isL2_ne_one hL2; omega
        rw [hd2] at hL2 hc₁ hc₂
        exact (w183b2_pair_gen_a5 Lb hL2 P₁ P₂ hP₁ hP₂ (by rw [hc₁]; norm_num)
          (by rw [hc₂]; norm_num) hP).2 a (hAP haE) b (hBP hbF) ha1 hb1
      · have hdle : d ≤ 2 := by omega
        have := w183b2_isSz_three_le hSz
        omega
      · obtain ⟨e⟩ := e
        have hd1 : d = 1 := w183b2_dihedral_d_eq_one hm e P₁ (by omega) hc₁
        rw [hd1] at hc₁ hc₂
        exact w183b2_pairabs_odd_dihedral hm e P₁ P₂ (by rw [hc₁]; norm_num)
          (by rw [hc₂]; norm_num) hP (hAP haE) ha1 (hBP hbF) hb1
    obtain ⟨a₀, ha₀Ah, ha₀⟩ := Subgroup.mem_map.mp haE
    obtain ⟨b₀, hb₀Bh, hb₀⟩ := Subgroup.mem_map.mp hbF
    have hEa : Ah.map π = Subgroup.zpowers a := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haE) ?_).symm
      rw [hEcard, Nat.card_zpowers, w183b2_orderOf_eq_two_of_card_eq_two hEcard haE ha1]
    have hFb : Bh.map π = Subgroup.zpowers b := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbF) ?_).symm
      rw [hFcard, Nat.card_zpowers, w183b2_orderOf_eq_two_of_card_eq_two hFcard hbF hb1]
    have ha2 : a * a = 1 := by
      have h2 := w183b2_orderOf_eq_two_of_card_eq_two hEcard haE ha1
      have := pow_orderOf_eq_one a
      rw [h2] at this
      simpa [pow_two] using this
    have hb2 : b * b = 1 := by
      have h2 := w183b2_orderOf_eq_two_of_card_eq_two hFcard hbF hb1
      have := pow_orderOf_eq_one b
      rw [h2] at this
      simpa [pow_two] using this
    have hAh : Ah = Subgroup.zpowers a₀ ⊔ (Ah ⊓ π.ker) := by
      refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr ha₀Ah) inf_le_left)
      intro x hx
      have hxE : π x ∈ Subgroup.zpowers a := by
        have hx' : π x ∈ Ah.map π := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rwa [hEa] at hx'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxE
      have hker : a₀ ^ (-n) * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_zpow, ha₀, ← hn]
        simp [← zpow_add]
      have h2 : a₀ ^ (-n) * x ∈ Ah ⊓ π.ker :=
        Subgroup.mem_inf.mpr ⟨Ah.mul_mem (Ah.zpow_mem ha₀Ah (-n)) hx, hker⟩
      have h3 := Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers a₀ n) h2
      rwa [show a₀ ^ n * (a₀ ^ (-n) * x) = x from by group] at h3
    have hBh : Bh = Subgroup.zpowers b₀ ⊔ (Bh ⊓ π.ker) := by
      refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hb₀Bh) inf_le_left)
      intro x hx
      have hxF : π x ∈ Subgroup.zpowers b := by
        have hx' : π x ∈ Bh.map π := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rwa [hFb] at hx'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxF
      have hker : b₀ ^ (-n) * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_zpow, hb₀, ← hn]
        simp [← zpow_add]
      have h2 : b₀ ^ (-n) * x ∈ Bh ⊓ π.ker :=
        Subgroup.mem_inf.mpr ⟨Bh.mul_mem (Bh.zpow_mem hb₀Bh (-n)) hx, hker⟩
      have h3 := Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers b₀ n) h2
      rwa [show b₀ ^ n * (b₀ ^ (-n) * x) = x from by group] at h3
    set X := ψ.range with hX
    set O := CFSG.pCore 2 ↥X with hO
    set q : ↥X →* Bar2 X := QuotientGroup.mk' O with hq
    let abar : ↥X := ψ.rangeRestrict a₀
    let bbar : ↥X := ψ.rangeRestrict b₀
    have hmap_eq : (π.ker).map ψ.rangeRestrict = ((π.ker).map ψ).subgroupOf X := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
        exact ⟨x, hx, Subtype.ext (by simpa using hxy)⟩
    have hNψ_le : ((π.ker).map ψ).subgroupOf X ≤ O := by
      apply w183b2_le_pCore_of_normal_isPGroup
      · have h1 : ((π.ker).map ψ.rangeRestrict).Normal :=
          (inferInstance : π.ker.Normal).map ψ.rangeRestrict ψ.rangeRestrict_surjective
        rwa [hmap_eq] at h1
      · have h1 : IsPGroup 2 ((π.ker).map ψ.rangeRestrict) := hK.map ψ.rangeRestrict
        rwa [hmap_eq] at h1
    let Ψ : Xh →* Bar2 X := q.comp ψ.rangeRestrict
    have hΨsurj : Function.Surjective Ψ :=
      (QuotientGroup.mk'_surjective O).comp ψ.rangeRestrict_surjective
    have hΨker : ((π.ker).map Ψ) = ⊥ := by
      rw [show Ψ = q.comp ψ.rangeRestrict from rfl, ← Subgroup.map_map, hmap_eq]
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hNψ_le
    have hker_le : π.ker ≤ Ψ.ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hΨker
    have hgen_bar : Subgroup.zpowers (q abar) ⊔ Subgroup.zpowers (q bbar) = ⊤ := by
      have hAh' : Ah.map Ψ = Subgroup.zpowers (q abar) ⊔ (Ah ⊓ π.ker).map Ψ := by
        conv_lhs => rw [hAh]
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
        rfl
      have hBh' : Bh.map Ψ = Subgroup.zpowers (q bbar) ⊔ (Bh ⊓ π.ker).map Ψ := by
        conv_lhs => rw [hBh]
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
        rfl
      have hAhk : (Ah ⊓ π.ker).map Ψ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact inf_le_right.trans hker_le
      have hBhk : (Bh ⊓ π.ker).map Ψ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact inf_le_right.trans hker_le
      have h1 : Ah.map Ψ ⊔ Bh.map Ψ = ⊤ := by
        rw [← Subgroup.map_sup, hgen]
        exact Subgroup.map_top_of_surjective Ψ hΨsurj
      rw [hAh', hBh', hAhk, hBhk] at h1
      simpa using h1
    have habar2 : q abar * q abar = 1 := by
      have hker : a₀ * a₀ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, ha₀, ha2]
      have hmem : ψ.rangeRestrict (a₀ * a₀) ∈ O := by
        apply hNψ_le
        rw [← hmap_eq]
        exact Subgroup.mem_map.mpr ⟨a₀ * a₀, hker, rfl⟩
      rw [← map_mul, show abar * abar = ψ.rangeRestrict (a₀ * a₀) from by simp [abar, map_mul]]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hbbar2 : q bbar * q bbar = 1 := by
      have hker : b₀ * b₀ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, hb₀, hb2]
      have hmem : ψ.rangeRestrict (b₀ * b₀) ∈ O := by
        apply hNψ_le
        rw [← hmap_eq]
        exact Subgroup.mem_map.mpr ⟨b₀ * b₀, hker, rfl⟩
      rw [← map_mul, show bbar * bbar = ψ.rangeRestrict (b₀ * b₀) from by simp [bbar, map_mul]]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hpow : (q abar * q bbar) ^ orderOf (a * b) = 1 := by
      have hker : (a₀ * b₀) ^ orderOf (a * b) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_pow, map_mul, ha₀, hb₀, pow_orderOf_eq_one]
      have hmem : ψ.rangeRestrict ((a₀ * b₀) ^ orderOf (a * b)) ∈ O := by
        apply hNψ_le
        rw [← hmap_eq]
        exact Subgroup.mem_map.mpr ⟨(a₀ * b₀) ^ orderOf (a * b), hker, rfl⟩
      have h1 : q abar * q bbar = q (ψ.rangeRestrict (a₀ * b₀)) := by
        rw [← map_mul]
        congr 1
        simp [abar, bbar, map_mul]
      have h2 : (q (ψ.rangeRestrict (a₀ * b₀))) ^ orderOf (a * b) =
          q (ψ.rangeRestrict ((a₀ * b₀) ^ orderOf (a * b))) := by
        rw [← map_pow]
        congr 1
        exact (map_pow ψ.rangeRestrict (a₀ * b₀) (orderOf (a * b))).symm
      rw [h1, h2]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    by_cases hcase : q abar = q bbar ∨ q abar = 1 ∨ q bbar = 1
    · have hbar2 : IsPGroup 2 (Bar2 X) := by
        rcases hcase with h | h | h
        · have hz : Subgroup.zpowers (q abar) = ⊤ := by
            rw [← hgen_bar, h, sup_idem]
          exact w183b2_isPGroup_of_zpowers_involution habar2 hz
        · have hz : Subgroup.zpowers (q bbar) = ⊤ := by
            rw [← hgen_bar, h, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
          exact w183b2_isPGroup_of_zpowers_involution hbbar2 hz
        · have hz : Subgroup.zpowers (q abar) = ⊤ := by
            rw [← hgen_bar, h, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
          exact w183b2_isPGroup_of_zpowers_involution habar2 hz
      refine Or.inl ⟨hk1, hk2, Or.inl ?_⟩
      exact w183b2_isPGroup_of_normal_isPGroup_quotient (p := 2) (N := O)
        (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) hbar2
    · have hne1 : q abar ≠ q bbar := (not_or.mp hcase).1
      have hne2 : q abar ≠ 1 := (not_or.mp (not_or.mp hcase).2).1
      have hne3 : q bbar ≠ 1 := (not_or.mp (not_or.mp hcase).2).2
      have hr_odd : Odd (orderOf (q abar * q bbar)) :=
        hodd.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hpow)
      have hr_gt : 1 < orderOf (q abar * q bbar) := by
        have hne : q abar * q bbar ≠ 1 := by
          intro h
          apply hne1
          calc q abar = q abar * (q bbar * q bbar) := by rw [hbbar2, mul_one]
            _ = (q abar * q bbar) * q bbar := by group
            _ = 1 * q bbar := by rw [h]
            _ = q bbar := one_mul _
        have hne' : orderOf (q abar * q bbar) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
        have hpos : 0 < orderOf (q abar * q bbar) := orderOf_pos _
        omega
      refine Or.inl ⟨hk1, hk2, Or.inr ⟨orderOf (q abar * q bbar), hr_odd, hr_gt, ?_⟩⟩
      have hgen_top : Subgroup.closure ({q abar, q bbar} : Set (Bar2 X)) = ⊤ := by
        rw [← hgen_bar, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
          ← Subgroup.closure_union]
        congr 1
      obtain ⟨e⟩ := w183b2_dihedral_of_involutions habar2 hbbar2 hne1 hne2 hne3
      rw [hgen_top] at e
      exact ⟨Subgroup.topEquiv.symm.trans e⟩
  · have hd3 : d ≤ 3 := by omega
    have hπrange : π.range = Ah.map π ⊔ Bh.map π := by
      rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup]
    have hπtop : π.range = ⊤ := by
      rcases hshape with hL2 | hSz | ⟨m, hm, e⟩
      · have hd2 : 2 ≤ d := by have := w183b2_isL2_ne_one hL2; omega
        have hdcase : d = 2 ∨ d = 3 := by omega
        rcases hdcase with h | h
        · rw [h] at hL2 hc₁ hc₂
          rw [hπrange]
          exact (w183b2_pair_gen_a5 Lb hL2 P₁ P₂ hP₁ hP₂ (by rw [hc₁]; norm_num)
            (by rw [hc₂]; norm_num) hP).1 (Ah.map π) (Bh.map π) hAP hBP
            (by rw [hAc, hBc]; exact w183b2_eight_le_pow_mul hk₁ hk₂ h11)
        · rw [h] at hL2 hc₁ hc₂
          rw [hπrange]
          refine (hL28 Lb hL2 P₁ P₂ hP₁ hP₂ (by rw [hc₁]; norm_num)
            (by rw [hc₂]; norm_num) hP).1 (Ah.map π) (Bh.map π) hAP hBP ?_ ?_
          · rw [hAc]; exact w183b2_four_le_pow_two (by omega)
          · rw [hBc]; exact w183b2_four_le_pow_two (by omega)
      · have h3 := w183b2_isSz_three_le hSz
        have hd3' : d = 3 := by omega
        rw [hd3'] at hSz hc₁ hc₂
        rw [hπrange]
        refine (hSz8 Lb hSz P₁ P₂ hP₁ hP₂ (by rw [hc₁]; norm_num)
          (by rw [hc₂]; norm_num) hP).1 (Ah.map π) (Bh.map π) hAP hBP ?_ ?_
        · rw [hAc]; exact w183b2_four_le_pow_two (by omega)
        · rw [hBc]; exact w183b2_four_le_pow_two (by omega)
      · exfalso
        obtain ⟨e⟩ := e
        have hd1 : d = 1 := w183b2_dihedral_d_eq_one hm e P₁ (by omega) hc₁
        omega
    rcases hshape with hL2 | hSz | ⟨m, hm, e⟩
    · have hπsurj : Function.Surjective π := MonoidHom.range_eq_top.mp hπtop
      have hLb_simple : IsSimpleGroup Lb :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
      have hd2 : 2 ≤ d := by have := w183b2_isL2_ne_one hL2; omega
      have hcardLb : Nat.card Lb = 60 ∨ Nat.card Lb = 504 := by
        have hdcase : d = 2 ∨ d = 3 := by omega
        rcases hdcase with h | h
        · left; rw [h] at hL2
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four
            (hL2.statedClassicalModel (by decide))
        · right; rw [h] at hL2
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
            (hL2.statedClassicalModel (by decide))
      have hψle : ψ.ker ≤ π.ker := by
        haveI : IsSolvable ψ.ker := hC
        have hmap_solv : IsSolvable ↥((ψ.ker).map π) := by
          have hrange : (π.comp (ψ.ker).subtype).range = (ψ.ker).map π := by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]
          rw [← hrange]
          exact @Group.isSolvable_of_surjective ↥ψ.ker
            ↥((π.comp (ψ.ker).subtype).range) _ _
            (π.comp (ψ.ker).subtype).rangeRestrict
            (π.comp (ψ.ker).subtype).rangeRestrict_surjective hC
        have hmap_normal : ((ψ.ker).map π).Normal :=
          (inferInstance : ψ.ker.Normal).map π hπsurj
        haveI := hmap_normal
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ψ.ker).map π) with h | h
        · rw [Subgroup.map_eq_bot_iff] at h; exact h
        · exfalso
          have htop : IsSolvable ↥(⊤ : Subgroup Lb) := by rw [h] at hmap_solv; exact hmap_solv
          have hsolv : IsSolvable Lb := by
            haveI : IsSolvable (⊤ : Subgroup Lb) := htop
            exact @Group.isSolvable_of_surjective (⊤ : Subgroup Lb) Lb _ _
              (Subgroup.topEquiv : (⊤ : Subgroup Lb) ≃* Lb).toMonoidHom
              Subgroup.topEquiv.surjective htop
          have hcomm : ∀ a b : Lb, a * b = b * a :=
            IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
          have hP1n : P₁.Normal := ⟨fun n hn g => by
            rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
          haveI := hP1n
          rcases Subgroup.Normal.eq_bot_or_eq_top P₁ with hbot | htop'
          · have h1 : Nat.card P₁ = 1 := by rw [hbot]; simp
            have h4 : 4 ≤ Nat.card P₁ := by rw [hc₁]; exact w183b2_four_le_pow_two hd2
            omega
          · have hcard : Nat.card P₁ = Nat.card Lb := by
              rw [htop']
              exact Nat.card_congr Subgroup.topEquiv.toEquiv
            have h8 : Nat.card P₁ ≤ 8 := by rw [hc₁]; exact Nat.pow_le_pow_right (by norm_num) hd3
            rcases hcardLb with h | h <;> omega
      set X := ψ.range with hX
      set N := ((π.ker).map ψ).subgroupOf X with hN
      have hN_eq : (π.ker).map ψ.rangeRestrict = N := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
        · intro hy
          obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
          exact ⟨x, hx, Subtype.ext (by simpa using hxy)⟩
      have hN2 : IsPGroup 2 N := by
        have h1 : IsPGroup 2 ((π.ker).map ψ.rangeRestrict) := hK.map ψ.rangeRestrict
        rwa [hN_eq] at h1
      have hNnormal : N.Normal := by
        have h1 : ((π.ker).map ψ.rangeRestrict).Normal :=
          (inferInstance : π.ker.Normal).map ψ.rangeRestrict ψ.rangeRestrict_surjective
        rwa [hN_eq] at h1
      haveI := hNnormal
      let hq : Xh →* ↥X ⧸ N := (QuotientGroup.mk' N).comp ψ.rangeRestrict
      have hq_surj : Function.Surjective hq :=
        (QuotientGroup.mk'_surjective N).comp ψ.rangeRestrict_surjective
      have hq_ker : hq.ker = π.ker := by
        have hcomap : hq.ker = ((π.ker).map ψ).comap ψ := by
          ext x
          change (ψ.rangeRestrict x : ↥X ⧸ N) = 1 ↔ ψ x ∈ (π.ker).map ψ
          rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          rfl
        rw [hcomap, Subgroup.comap_map_eq_self hψle]
      have e1 : Xh ⧸ π.ker ≃* ↥X ⧸ N :=
        (QuotientGroup.quotientMulEquivOfEq hq_ker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective hq hq_surj)
      let e : Lb ≃* ↥X ⧸ N := (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).symm.trans e1
      have hQ2 : ¬ IsPGroup 2 Lb := by
        intro hp
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
        have h3 : 3 ∣ Nat.card Lb := by
          rcases hcardLb with h | h <;> rw [h] <;> norm_num
        rw [hn] at h3
        have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
        norm_num at h32
      have hpCore : CFSG.pCore 2 ↥X = N :=
        w183b2_pCore_eq_of_simple_quotient hN2 hQ2 e.symm
      have hcardBar2 : Nat.card (Bar2 X) = Nat.card Lb := by
        have h1 : Nat.card (Bar2 X) = Nat.card (↥X ⧸ N) := by
          change Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = Nat.card (↥X ⧸ N)
          rw [hpCore]
        rw [h1]
        exact (Nat.card_congr e.toEquiv).symm
      have hdcase : d = 2 ∨ d = 3 := by omega
      rcases hdcase with hd | hd
      · have h60 : Nat.card Lb = 60 := by
          rw [hd] at hL2
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four
            (hL2.statedClassicalModel (by decide))
        by_cases hk : k₁ + k₂ = 3
        · exact Or.inr (Or.inl ⟨hk, by rw [hcardBar2, h60]⟩)
        · exact Or.inr (Or.inr ⟨by omega, by omega, Or.inl (by rw [hcardBar2, h60])⟩)
      · have h504 : Nat.card Lb = 504 := by
          rw [hd] at hL2
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight
            (hL2.statedClassicalModel (by decide))
        exact Or.inr (Or.inr ⟨by omega, by omega, Or.inr (by rw [hcardBar2, h504])⟩)
    · have hd3' : d = 3 := by have := w183b2_isSz_three_le hSz; omega
      exact (w183b2_pair_abs_isSz_excluded π hK ψ hC h13 (by rw [hd3'] at hSz; exact hSz)
        hπtop).elim
    · exfalso
      obtain ⟨e⟩ := e
      have hd1 : d = 1 := w183b2_dihedral_d_eq_one hm e P₁ (by omega) hc₁
      omega

end CFSG.LocalAnalysis.WeakClosure81

end
