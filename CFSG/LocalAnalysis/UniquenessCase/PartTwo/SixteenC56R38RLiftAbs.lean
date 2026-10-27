module

public import CFSG.RankThree.GroupTheory.PerfectSubnormalModNormal
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped commutatorElement

theorem le_normalizer_of_perfect_cover {G : Type*} [Group G] [Finite G] {X C Y : Subgroup G}
    (hYX : Y ≤ X) (hCX : C ≤ X) (hYn : X ≤ normalizer (Y : Set G))
    (hCn : X ≤ normalizer (C : Set G)) (hperf : ⁅Y, Y⁆ = Y) (hcov : Y ⊔ C = X)
    (hsol : Group.IsSolvable ↥(Y ⊓ C)) {g : G} (hgX : g ∈ normalizer (X : Set G))
    (hgC : g ∈ normalizer (C : Set G)) : g ∈ normalizer (Y : Set G) := by
  set c : G ≃* G := MulAut.conj g with hc
  set Y' : Subgroup G := Y.map c with hY'
  have hXmap : X.map c = X := by
    rw [hc]; exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgX
  have hCmap : C.map c = C := by
    rw [hc]; exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgC
  have hYX' : Y' ≤ X := by
    rw [hY']; exact (Subgroup.map_mono hYX).trans_eq hXmap
  have hmem : ∀ y : G, y ∈ Y' ↔ g⁻¹ * y * g ∈ Y := by
    intro y
    rw [hY', Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hay⟩
      rw [hc] at hay
      change MulAut.conj g a = y at hay
      have : a = g⁻¹ * y * g := by rw [← hay, MulAut.conj_apply]; group
      rw [← this]; exact ha
    · intro hy
      refine ⟨g⁻¹ * y * g, hy, ?_⟩
      rw [hc]
      change MulAut.conj g (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group
  have hgXi : g⁻¹ ∈ normalizer (X : Set G) := Subgroup.inv_mem _ hgX
  have hnorm' : X ≤ normalizer (Y' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem y, hmem (x * y * x⁻¹)]
    have hxX : g⁻¹ * x * g ∈ X := by
      have h := (Subgroup.mem_normalizer_iff.mp hgXi x).mp hx
      simpa using h
    have e : g⁻¹ * (x * y * x⁻¹) * g =
        (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYn hxX) (g⁻¹ * y * g))
  have hY'C : Y' ⊔ C = X := by
    rw [hY', ← hCmap, ← Subgroup.map_sup, hcov, hXmap]
  have hsup1 : Y.subgroupOf X ⊔ C.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hYX hCX, hcov, Subgroup.subgroupOf_self]
  have hsup2 : Y'.subgroupOf X ⊔ C.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hYX' hCX, hY'C, Subgroup.subgroupOf_self]
  haveI hYperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hY0perf : Group.IsPerfect ↥(Y.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYX).symm.surjective
  have hY'perf : Group.IsPerfect ↥Y' := by
    rw [hY']; exact Group.IsPerfect.map (f := c.toMonoidHom)
  have hY'0perf : Group.IsPerfect ↥(Y'.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYX').symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYX').symm.surjective
  have hinf : (Y ⊓ C).subgroupOf X = Y.subgroupOf X ⊓ C.subgroupOf X :=
    Subgroup.comap_inf Y C X.subtype
  have hsol0 : Group.IsSolvable ↥(Y.subgroupOf X ⊓ C.subgroupOf X) := by
    rw [← hinf]
    haveI : Group.IsSolvable ↥(Y ⊓ C) := hsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYX)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYX)).injective
  haveI hY0n : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hYn
  haveI hC0n : (C.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hCn
  haveI hY'0n : (Y'.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX').mpr hnorm'
  have hsup : Y.subgroupOf X ⊔ C.subgroupOf X = Y'.subgroupOf X ⊔ C.subgroupOf X :=
    hsup1.trans hsup2.symm
  have hle0 : Y.subgroupOf X ≤ Y'.subgroupOf X :=
    CFSG.RankThree.GroupTheory.le_of_perfect_of_sup_eq_of_solvable_inf
      (S₁ := Y.subgroupOf X) (S₂ := Y'.subgroupOf X) (R := C.subgroupOf X)
      hY0perf (Subgroup.le_normalizer_of_normal (H := Y.subgroupOf X))
      (Subgroup.le_normalizer_of_normal (H := Y'.subgroupOf X)) hsup hsol0
  have hle : Y ≤ Y' := by
    intro y hy
    exact hle0 (show (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X from hy)
  have hcard : Nat.card ↥Y' = Nat.card ↥Y := by
    rw [hY']
    exact Subgroup.card_map_of_injective (by rw [hc]; exact (MulAut.conj g).injective)
  have hEq : Y = Y' := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  have hthis : Y.map c = Y := by rw [← hY']; exact hEq.symm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by rw [hc] at hthis; exact hthis)

theorem exists_sylow_lift_commuting {M H : Type*} [Group M] [Finite M] [Group H] (π : M →* H)
    {Lst : Subgroup M} (hLn : Lst.Normal) {q : ℕ} (hq : q.Prime)
    (hLC : ¬ q ∣ Nat.card ↥(Lst ⊓ π.ker)) {a : M} (ha : ∃ k : ℕ, a ^ (q ^ k) = 1)
    {T : Subgroup H} (hTL : T ≤ Lst.map π) (hT : IsElemAbelian q T)
    (hTa : ∀ t ∈ T, π a * t = t * π a) :
    ∃ D : Subgroup M, D ≤ Lst ∧ D ⊓ π.ker = ⊥ ∧ D.map π = T ∧ ∀ d ∈ D, a * d = d * a := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hLmapFin : Finite ↥(Lst.map π) :=
    Finite.of_surjective (fun x : ↥Lst => (⟨π x, ⟨x, x.2, rfl⟩⟩ : ↥(Lst.map π)))
      (by
        intro y
        obtain ⟨l, hl, hlπ⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨l, hl⟩, Subtype.ext hlπ⟩)
  have hTfin : Finite ↥T :=
    Finite.of_injective (Subgroup.inclusion hTL) (Subgroup.inclusion_injective hTL)
  haveI := hTfin
  set LT : Subgroup M := Lst ⊓ T.comap π with hLT
  have hLTmap : LT.map π = T := by
    apply le_antisymm
    · rintro t ⟨l, hl, rfl⟩
      rw [hLT] at hl
      exact hl.2
    · intro t ht
      obtain ⟨l, hl, hlπ⟩ := Subgroup.mem_map.mp (hTL ht)
      exact ⟨l, by rw [hLT]; exact ⟨hl, by change π l ∈ T; rw [hlπ]; exact ht⟩, hlπ⟩
  have hker_le : π.ker ≤ T.comap π := by
    intro x hx
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact T.one_mem)
  have hLTker : LT ⊓ π.ker = Lst ⊓ π.ker := by
    rw [hLT]
    apply le_antisymm
    · intro x hx; exact ⟨hx.1.1, hx.2⟩
    · intro x hx; exact ⟨⟨hx.1, hker_le hx.2⟩, hx.2⟩
  have hcardLT : Nat.card ↥LT = Nat.card ↥T * Nat.card ↥(Lst ⊓ π.ker) := by
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict LT)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, hLTmap] at h
    have hk : Nat.card ↥(π.ker.subgroupOf LT) = Nat.card ↥(Lst ⊓ π.ker) := by
      rw [← Subgroup.inf_subgroupOf_right (π.ker) LT]
      rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : π.ker ⊓ LT ≤ LT)).toEquiv]
      rw [inf_comm, hLTker]
    rw [hk, mul_comm] at h
    exact h.symm
  have hTp : IsPGroup q ↥T := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hT.2 x.1 x.2)
  have hLTq : q ^ (Nat.card ↥LT).factorization q = Nat.card ↥T := by
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hTp
    have hfac : (Nat.card ↥LT).factorization q = n := by
      rw [hcardLT, hn]
      rw [Nat.factorization_mul (pow_ne_zero n hq.ne_zero) Nat.card_pos.ne']
      rw [Finsupp.add_apply, Nat.factorization_pow_self hq,
        Nat.factorization_eq_zero_of_not_dvd hLC, add_zero]
    rw [hfac, hn]
  have hconj_in : ∀ t ∈ T, π a * t * (π a)⁻¹ ∈ T := by
    intro t ht
    rw [hTa t ht, mul_assoc, mul_inv_cancel, mul_one]
    exact ht
  have hconj_in_inv : ∀ t ∈ T, (π a)⁻¹ * t * π a ∈ T := by
    intro t ht
    have e : (π a)⁻¹ * t * π a = t := by
      rw [mul_assoc, ← hTa t ht, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]; exact ht
  have hconj_out : ∀ t, π a * t * (π a)⁻¹ ∈ T → t ∈ T := by
    intro t ht
    have h := hconj_in_inv (π a * t * (π a)⁻¹) ht
    have e : (π a)⁻¹ * (π a * t * (π a)⁻¹) * π a = t := by group
    rwa [e] at h
  have ha_nLst : a ∈ normalizer (Lst : Set M) := by
    rw [Subgroup.normalizer_eq_top (H := Lst)]; trivial
  have ha_ncomap : a ∈ normalizer (T.comap π : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact ⟨hconj_in (π x), hconj_out (π x)⟩
  have ha_nLT : a ∈ normalizer (LT : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hLT, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp ha_nLst x).mp hx1,
        (Subgroup.mem_normalizer_iff.mp ha_ncomap x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp ha_nLst x).mpr hx1,
        (Subgroup.mem_normalizer_iff.mp ha_ncomap x).mpr hx2⟩
  have hnorm : ∀ m ∈ LT ⊔ Subgroup.zpowers a, ∀ x ∈ LT, m * x * m⁻¹ ∈ LT := by
    have hle : LT ⊔ Subgroup.zpowers a ≤ normalizer (LT : Set M) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr ha_nLT)
    intro m hm x hx
    exact (Subgroup.mem_normalizer_iff.mp (hle hm) x).mp hx
  have hzaP : IsPGroup q ↥(Subgroup.zpowers a) := by
    obtain ⟨k, hk⟩ := ha
    exact IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨Qs, _hQsHh, haQs, hQsP, hQsLT⟩ :=
    CFSG.GH74.GLS.IVK.exists_pGroup_inf_sylow q (LT ⊔ Subgroup.zpowers a) LT
      (Subgroup.zpowers a) le_sup_left le_sup_right hnorm hzaP
  rw [hLTq] at hQsLT
  have haQs' : a ∈ Qs := haQs (Subgroup.mem_zpowers a)
  set D : Subgroup M := Qs ⊓ LT with hD
  have hDLst : D ≤ Lst := by
    intro x hx
    rw [hD] at hx
    rw [hLT] at hx
    exact hx.2.1
  have hDp : IsPGroup q ↥D := by
    rw [hD]; exact hQsP.to_le inf_le_left
  have hDker : D ⊓ π.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hxLst : x ∈ Lst := by
      have hxLst' : x ∈ LT := hx.1.2
      rw [hLT] at hxLst'
      exact hxLst'.1
    have hdiv : q ∣ Nat.card ↥(Lst ⊓ π.ker) := by
      have h1 : q ∣ orderOf x := by
        have h2 : q ∣ orderOf (⟨x, hx.1⟩ : ↥D) :=
          hDp.dvd_orderOf (by
            intro h; exact hx1 (Subtype.ext_iff.mp h))
        rwa [Subgroup.orderOf_mk x hx.1] at h2
      exact h1.trans (Subgroup.orderOf_dvd_natCard (Lst ⊓ π.ker) ⟨hxLst, hx.2⟩)
    exact hLC hdiv
  have hDmap_le : D.map π ≤ T := by
    have h := Subgroup.map_mono (f := π) (show D ≤ LT from by rw [hD]; exact inf_le_right)
    rwa [hLTmap] at h
  have hDcard : Nat.card ↥(D.map π) = Nat.card ↥D := by
    have hker_bot : (π.domRestrict D).ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      change π (x : M) = 1 at hx
      have hx' : (x : M) ∈ D ⊓ π.ker := ⟨x.2, hx⟩
      rw [hDker] at hx'
      exact Subtype.ext (Subgroup.mem_bot.mp hx')
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict D)
    rw [hker_bot, MonoidHom.domRestrict_range] at h
    simpa [Subgroup.card_bot] using h
  have hDT : Nat.card ↥D = Nat.card ↥T := by
    rw [hD]; exact hQsLT
  have hDmap : D.map π = T :=
    Subgroup.eq_of_le_of_card_ge hDmap_le (by rw [hDcard, hDT])
  have hcomm : ∀ d ∈ D, a * d = d * a := by
    intro d hd
    have hmem : a * d * a⁻¹ * d⁻¹ ∈ D :=
      ⟨Qs.mul_mem (Qs.mul_mem (Qs.mul_mem haQs' hd.1) (Qs.inv_mem haQs')) (Qs.inv_mem hd.1),
        LT.mul_mem ((Subgroup.mem_normalizer_iff.mp ha_nLT d).mp hd.2) (LT.inv_mem hd.2)⟩
    have hker : a * d * a⁻¹ * d⁻¹ ∈ π.ker := by
      change π (a * d * a⁻¹ * d⁻¹) = 1
      simp only [map_mul, map_inv]
      have hdT : π d ∈ T := by rw [← hDmap]; exact ⟨d, hd, rfl⟩
      rw [hTa (π d) hdT]
      group
    have h1 : a * d * a⁻¹ * d⁻¹ = 1 := by
      have hbot : a * d * a⁻¹ * d⁻¹ ∈ (⊥ : Subgroup M) := by
        rw [← hDker]; exact ⟨hmem, hker⟩
      exact Subgroup.mem_bot.mp hbot
    have h2 : a * d * a⁻¹ = d := mul_inv_eq_one.mp h1
    calc a * d = a * d * a⁻¹ * a := by group
      _ = d * a := by rw [h2]
  exact ⟨D, hDLst, hDker, hDmap, hcomm⟩

private lemma exists_ppart_of_lift {M H : Type*} [Group M] [Finite M] [Group H] (f : M →* H)
    {q : ℕ} (hq : q.Prime) {m : M} {s : ℕ} (hs : f m ^ (q ^ s) = 1) :
    ∃ g ∈ Subgroup.zpowers m, (∃ e : ℕ, g ^ (q ^ e) = 1) ∧ f g = f m := by
  have hn : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨e, b, hpb, hnb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  have hcop : Nat.Coprime b (q ^ s) :=
    Nat.Coprime.pow_right s ((Nat.Prime.coprime_iff_not_dvd hq).mpr hpb).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨m ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers m) k, ⟨e, ?_⟩, ?_⟩
  · have hb : b ∣ k := (Nat.modEq_zero_iff_dvd.mp hk1)
    obtain ⟨c, hc⟩ := hb
    rw [← pow_mul, hc]
    have : m ^ (b * c * q ^ e) = (m ^ orderOf m) ^ c := by
      rw [← pow_mul]
      congr 1
      rw [hnb]; ring
    rw [this, pow_orderOf_eq_one, one_pow]
  · rw [map_pow]
    have h1 : orderOf (f m) ∣ q ^ s := orderOf_dvd_of_pow_eq_one hs
    have h2 : k ≡ 1 [MOD orderOf (f m)] := Nat.ModEq.of_dvd h1 hk2
    have := (pow_eq_pow_iff_modEq (x := f m) (n := k) (m := 1)).mpr h2
    rw [this, pow_one]

private lemma exists_pow_orderOf_eq_prime_of_pow {G : Type*} [Group G] {q : ℕ} (hq : q.Prime)
    {w : G} {a : ℕ} (hw : w ^ (q ^ a) = 1) (hw1 : w ≠ 1) :
    ∃ k : ℕ, orderOf (w ^ k) = q := by
  obtain ⟨b', _hb'm, hb'⟩ := (Nat.dvd_prime_pow hq).1 (orderOf_dvd_of_pow_eq_one hw)
  have hb'1 : 1 ≤ b' := by
    by_contra hb0
    have : b' = 0 := by omega
    rw [this, pow_zero] at hb'
    exact hw1 (orderOf_eq_one_iff.1 hb')
  refine ⟨q ^ (b' - 1), ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hq.ne_zero)
      (by rw [hb']; exact pow_dvd_pow q (by omega)), hb']
  rw [Nat.pow_div (by omega : b' - 1 ≤ b') hq.pos]
  have : b' - (b' - 1) = 1 := by omega
  rw [this, pow_one]

theorem exists_isElemAbelian_card_eq_of_lift {M H : Type*} [Group M] [Finite M] [Group H]
    (π : M →* H) {Lst : Subgroup M} (hLn : Lst.Normal) {q : ℕ} (hq : q.Prime)
    (hLC : ¬ q ∣ Nat.card ↥(Lst ⊓ π.ker)) (a : M) {E : Subgroup H} (hE : IsElemAbelian q E)
    (haE : π a ∈ E) (hEle : E ≤ Lst.map π ⊔ Subgroup.zpowers (π a)) :
    ∃ F : Subgroup M, IsElemAbelian q F ∧ Nat.card F = Nat.card E := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hπaq : (π a) ^ q = 1 := hE.2 (π a) haE
  have hπaq1 : (π a) ^ (q ^ 1) = 1 := by simpa using hπaq
  obtain ⟨b, _hbzp, hbq, hbπ⟩ := exists_ppart_of_lift π hq hπaq1
  set T : Subgroup H := E ⊓ Lst.map π with hTdef
  have hTE_mem : ∀ {x : H}, x ∈ T → x ∈ E := by
    intro x hx; rw [hTdef] at hx; exact hx.1
  have hTL_mem : ∀ {x : H}, x ∈ T → x ∈ Lst.map π := by
    intro x hx; rw [hTdef] at hx; exact hx.2
  have hTle : T ≤ Lst.map π := fun _ hx => hTL_mem hx
  have hTea : IsElemAbelian q T :=
    ⟨⟨⟨fun x y => Subtype.ext (hE.comm (hTE_mem x.2) (hTE_mem y.2))⟩⟩,
      fun x hx => hE.2 x (hTE_mem hx)⟩
  have hTcent : ∀ t ∈ T, π b * t = t * π b := by
    intro t ht
    rw [hbπ]
    exact hE.comm haE (hTE_mem ht)
  obtain ⟨D, _hDLst, hDker, hDmap, hDcomm⟩ :=
    exists_sylow_lift_commuting π hLn hq hLC hbq hTle hTea hTcent
  have hDinj : Function.Injective (π.domRestrict D) := by
    intro x y hxy
    have hxy' : π (x : M) = π (y : M) := hxy
    have hmem : (x : M)⁻¹ * (y : M) ∈ D ⊓ π.ker := by
      refine ⟨D.mul_mem (D.inv_mem x.2) y.2, ?_⟩
      change π ((x : M)⁻¹ * (y : M)) = 1
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    rw [hDker] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem))
  have hDel : IsElemAbelian q D := by
    refine ⟨⟨⟨fun x y => hDinj ?_⟩⟩, fun x hx => ?_⟩
    · show (π.domRestrict D) (x * y) = (π.domRestrict D) (y * x)
      change π ((x : M) * (y : M)) = π ((y : M) * (x : M))
      rw [map_mul, map_mul]
      exact hTea.comm (by rw [← hDmap]; exact ⟨x, x.2, rfl⟩)
        (by rw [← hDmap]; exact ⟨y, y.2, rfl⟩)
    · have hxT : π x ∈ T := by rw [← hDmap]; exact ⟨x, hx, rfl⟩
      have hmem : x ^ q ∈ D ⊓ π.ker := by
        refine ⟨D.pow_mem hx q, ?_⟩
        change π (x ^ q) = 1
        rw [map_pow, hTea.2 (π x) hxT]
      rw [hDker] at hmem
      exact Subgroup.mem_bot.mp hmem
  have hDcardT : Nat.card ↥D = Nat.card ↥T := by
    have hker_bot : (π.domRestrict D).ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      change π (x : M) = 1 at hx
      have hx' : (x : M) ∈ D ⊓ π.ker := ⟨x.2, hx⟩
      rw [hDker] at hx'
      exact Subtype.ext (Subgroup.mem_bot.mp hx')
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict D)
    rw [hker_bot, MonoidHom.domRestrict_range, hDmap] at h
    simpa [Subgroup.card_bot] using h.symm
  by_cases hcase : π a ∈ Lst.map π
  · have hEsub : E ≤ Lst.map π :=
      hEle.trans (sup_le le_rfl (Subgroup.zpowers_le.mpr hcase))
    have hTE : T = E := by rw [hTdef]; exact inf_eq_left.mpr hEsub
    exact ⟨D, hDel, by rw [hDcardT, hTE]⟩
  · have hnot : π a ∉ Lst.map π := hcase
    have hπane : π a ≠ 1 := fun h => hnot (h ▸ (Lst.map π).one_mem)
    have hordπa : orderOf (π a) = q := orderOf_eq_prime hπaq hπane
    have hbne : b ≠ 1 := by
      intro h
      exact hπane (by rw [← hbπ, h, map_one])
    obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_prime_of_pow hq (Classical.choose_spec hbq) hbne
    let a₂ : M := b ^ k
    have horda₂ : orderOf a₂ = q := hk
    have ha₂comm_d : ∀ d ∈ D, Commute a₂ d := fun d hd =>
      (show Commute b d from hDcomm d hd).pow_left k
    have ha₂comm : ∀ x ∈ Subgroup.zpowers a₂, ∀ d ∈ D, x * d = d * x := by
      intro x hx d hd
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (ha₂comm_d d hd).zpow_left i
    have hπa₂_zpow : π a₂ ∈ Subgroup.zpowers (π a) := by
      rw [show a₂ = b ^ k from rfl, map_pow, hbπ]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (π a)) k
    have ha₂notD : a₂ ∉ D := by
      intro ha₂D
      have hπa₂T : π a₂ ∈ T := by rw [← hDmap]; exact ⟨a₂, ha₂D, rfl⟩
      have hπa₂Lb : π a₂ ∈ Lst.map π := hTL_mem hπa₂T
      by_cases hπa₂one : π a₂ = 1
      · have hmem : a₂ ∈ D ⊓ π.ker := ⟨ha₂D, hπa₂one⟩
        rw [hDker] at hmem
        have h1 : a₂ = 1 := Subgroup.mem_bot.mp hmem
        have h2 : q = 1 := by rw [h1] at horda₂; simpa using horda₂.symm
        exact hq.ne_one h2
      · have hmem : π a ∈ Subgroup.zpowers (π a₂) := by
          haveI : Finite ↥(Subgroup.zpowers (π a)) :=
            Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hordπa]; exact hq.ne_zero)
          have hEqZ : Subgroup.zpowers (π a₂) = Subgroup.zpowers (π a) := by
            apply Subgroup.eq_of_le_of_card_ge
            · exact Subgroup.zpowers_le.mpr hπa₂_zpow
            · rw [Nat.card_zpowers, Nat.card_zpowers, hordπa]
              have heq : π a₂ = (π a) ^ k := by
                rw [show a₂ = b ^ k from rfl, map_pow, hbπ]
              have hdvd : orderOf (π a₂) ∣ q := by
                have h1 : orderOf (π a₂) ∣ orderOf (π a) := by
                  rw [heq]; exact orderOf_pow_dvd k
                rwa [hordπa] at h1
              rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
              · exact absurd (orderOf_eq_one_iff.mp h1) hπa₂one
              · rw [h1]
          rw [hEqZ]; exact Subgroup.mem_zpowers (π a)
        exact hnot (Subgroup.zpowers_le.mpr hπa₂Lb hmem)
    have hdisj : Disjoint (Subgroup.zpowers a₂) D := by
      rw [Subgroup.disjoint_def]
      intro x hx₁ hx₂
      by_contra hx1
      haveI : Finite ↥(Subgroup.zpowers a₂) :=
        Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, horda₂]; exact hq.ne_zero)
      have hmem : (⟨a₂, Subgroup.mem_zpowers a₂⟩ : ↥(Subgroup.zpowers a₂)) ∈
          Subgroup.zpowers (⟨x, hx₁⟩ : ↥(Subgroup.zpowers a₂)) := by
        apply mem_zpowers_of_prime_card (p := q)
        · rw [Nat.card_zpowers, horda₂]
        · intro h; exact hx1 (Subtype.ext_iff.mp h)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hi' : x ^ i = a₂ := congrArg Subtype.val hi
      have : a₂ ∈ Subgroup.zpowers x := Subgroup.mem_zpowers_iff.mpr ⟨i, hi'⟩
      exact ha₂notD (Subgroup.zpowers_le.mpr hx₂ this)
    have hnormal : D ≤ Subgroup.normalizer (Subgroup.zpowers a₂ : Set M) := by
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h := ha₂comm x hx d hd
        have e : d * x * d⁻¹ = x := by rw [← h]; group
        rwa [e]
      · intro hx
        have hw : Commute (d * x * d⁻¹) d := ha₂comm (d * x * d⁻¹) hx d hd
        have e : x = d⁻¹ * (d * x * d⁻¹) * d := by group
        have e2 : d⁻¹ * (d * x * d⁻¹) * d = d * x * d⁻¹ := by
          rw [mul_assoc, hw, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [e, e2]; exact hx
    have hFcard : Nat.card ↥(Subgroup.zpowers a₂ ⊔ D) = q * Nat.card ↥D := by
      have h := CFSG.GH74.GLS.IVK.card_sup_of_le_normalizer
        (Subgroup.zpowers a₂) D hnormal hdisj
      rw [h, Nat.card_zpowers, horda₂]
    have hLnorm : π a ∈ Subgroup.normalizer (Lst.map π : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨a * l * a⁻¹, hLn.conj_mem l hl a, by rw [map_mul, map_mul, map_inv]⟩
      · rintro ⟨l', hl', hl'eq⟩
        refine ⟨a⁻¹ * l' * a, hLn.conj_mem' l' hl' a, ?_⟩
        rw [map_mul, map_mul, map_inv]
        have hy : y = (π a)⁻¹ * π l' * π a := by rw [hl'eq]; group
        rw [hy]
    have hpaE : π a ∈ Subgroup.normalizer (E : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have e : π a * z * (π a)⁻¹ = z := by rw [hE.comm haE hz]; group
        rwa [e]
      · intro hz
        have hw : π a * z * (π a)⁻¹ ∈ E := hz
        have e : (π a)⁻¹ * (π a * z * (π a)⁻¹) * π a = π a * z * (π a)⁻¹ := by
          rw [hE.comm (E.inv_mem haE) hw]; group
        rw [show z = (π a)⁻¹ * (π a * z * (π a)⁻¹) * π a from by group, e]
        exact hw
    have hpaT : π a ∈ Subgroup.normalizer (T : Set H) := by
      rw [hTdef]
      exact Subgroup.inf_normalizer_le_normalizer_inf (H := E) (K := Lst.map π)
        ⟨hpaE, hLnorm⟩
    have hle' : Subgroup.zpowers (π a) ≤ Subgroup.normalizer (Lst.map π : Set H) :=
      Subgroup.zpowers_le.mpr hLnorm
    have hLbdisj : Lst.map π ⊓ Subgroup.zpowers (π a) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hx1
      have hcard : Nat.card ↥(Subgroup.zpowers (π a)) = q := by rw [Nat.card_zpowers, hordπa]
      have hxg : (⟨x, hx.2⟩ : ↥(Subgroup.zpowers (π a))) ≠ 1 := by
        intro h; exact hx1 (Subtype.ext_iff.mp h)
      have hmem : (⟨π a, Subgroup.mem_zpowers (π a)⟩ : ↥(Subgroup.zpowers (π a))) ∈
          Subgroup.zpowers (⟨x, hx.2⟩ : ↥(Subgroup.zpowers (π a))) :=
        mem_zpowers_of_prime_card hcard hxg
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hi' : x ^ i = π a := congrArg Subtype.val hi
      have : π a ∈ Subgroup.zpowers x := Subgroup.mem_zpowers_iff.mpr ⟨i, hi'⟩
      exact hnot (Subgroup.zpowers_le.mpr hx.1 this)
    have hdisjT : Disjoint T (Subgroup.zpowers (π a)) := by
      rw [Subgroup.disjoint_def]
      intro x hxT hxz
      have hx' : x ∈ Lst.map π ⊓ Subgroup.zpowers (π a) := ⟨hTL_mem hxT, hxz⟩
      rw [hLbdisj] at hx'
      exact Subgroup.mem_bot.mp hx'
    have hEeq : E = T ⊔ Subgroup.zpowers (π a) := by
      apply le_antisymm
      · intro e he
        have he' : e ∈ ((Lst.map π ⊔ Subgroup.zpowers (π a) : Subgroup H) : Set H) := hEle he
        rw [Subgroup.coe_mul_of_right_le_normalizer_left (Lst.map π)
          (Subgroup.zpowers (π a)) hle'] at he'
        obtain ⟨l, hl, z, hz, hlz⟩ := he'
        have hlE : l ∈ E := by
          have : l = e * z⁻¹ := by rw [← hlz]; group
          rw [this]
          exact E.mul_mem he ((Subgroup.zpowers_le.mpr haE) (Subgroup.inv_mem _ hz))
        have hlT : l ∈ T := by rw [hTdef]; exact ⟨hlE, hl⟩
        rw [← hlz]
        exact mul_mem_sup hlT hz
      · rw [hTdef]
        exact sup_le inf_le_left (Subgroup.zpowers_le.mpr haE)
    have hEcard : Nat.card ↥E = q * Nat.card ↥T := by
      have h := CFSG.GH74.GLS.IVK.card_sup_of_le_normalizer T (Subgroup.zpowers (π a))
        (Subgroup.zpowers_le.mpr hpaT) hdisjT
      rw [hEeq, h, Nat.card_zpowers, hordπa, Nat.mul_comm]
    have hF1 : IsElemAbelian q (Subgroup.zpowers a₂) :=
      CFSG.Open.isElemAbelian_zpowers (by rw [← horda₂]; exact pow_orderOf_eq_one a₂)
    exact ⟨Subgroup.zpowers a₂ ⊔ D,
      CFSG.Open.IsElemAbelian.sup_of_commute hF1 hDel ha₂comm, by rw [hFcard, hDcardT, hEcard]⟩

private lemma map_mem_normalizer_map {M H : Type*} [Group M] [Group H] (π : M →* H)
    {Lst : Subgroup M} (hLn : Lst.Normal) (x : M) :
    π x ∈ Subgroup.normalizer (Lst.map π : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨x * l * x⁻¹, hLn.conj_mem l hl x, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨l', hl', hl'eq⟩
    refine ⟨x⁻¹ * l' * x, hLn.conj_mem' l' hl' x, ?_⟩
    rw [map_mul, map_mul, map_inv]
    have hy : y = (π x)⁻¹ * π l' * π x := by rw [hl'eq]; group
    rw [hy]

private lemma inf_map_zpowers_eq_bot_of_notMem {M H : Type*} [Group M] [Group H] (π : M →* H)
    {Lst : Subgroup M} {q : ℕ} (hq : q.Prime) {a : M} (hnot : π a ∉ Lst.map π)
    (hord : orderOf (π a) = q) : Lst.map π ⊓ Subgroup.zpowers (π a) = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  have hcard : Nat.card ↥(Subgroup.zpowers (π a)) = q := by rw [Nat.card_zpowers, hord]
  haveI : Finite ↥(Subgroup.zpowers (π a)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have hxg : (⟨x, hx.2⟩ : ↥(Subgroup.zpowers (π a))) ≠ 1 := by
    intro h; exact hx1 (Subtype.ext_iff.mp h)
  have hmem : (⟨π a, Subgroup.mem_zpowers (π a)⟩ : ↥(Subgroup.zpowers (π a))) ∈
      Subgroup.zpowers (⟨x, hx.2⟩ : ↥(Subgroup.zpowers (π a))) :=
    mem_zpowers_of_prime_card hcard hxg
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hi' : x ^ i = π a := congrArg Subtype.val hi
  have : π a ∈ Subgroup.zpowers x := Subgroup.mem_zpowers_iff.mpr ⟨i, hi'⟩
  exact hnot (Subgroup.zpowers_le.mpr hx.1 this)

theorem exists_isElemAbelian_map_eq_of_lift {M H : Type*} [Group M] [Finite M] [Group H]
    (π : M →* H) {Lst : Subgroup M} (hLn : Lst.Normal) {q : ℕ} (hq : q.Prime)
    (hLC : ¬ q ∣ Nat.card ↥(Lst ⊓ π.ker)) {a : M} (ha : a ^ q = 1) (hnot : π a ∉ Lst.map π)
    {E : Subgroup H} (hE : IsElemAbelian q E) (haE : π a ∈ E)
    (hEle : E ≤ Lst.map π ⊔ Subgroup.zpowers (π a)) :
    ∃ F : Subgroup M, IsElemAbelian q F ∧ a ∈ F ∧ F ⊓ π.ker = ⊥ ∧ F.map π = E := by
  haveI : Fact q.Prime := ⟨hq⟩
  set T : Subgroup H := E ⊓ Lst.map π with hTdef
  have hTE_mem : ∀ {x : H}, x ∈ T → x ∈ E := by
    intro x hx; rw [hTdef] at hx; exact hx.1
  have hTL_mem : ∀ {x : H}, x ∈ T → x ∈ Lst.map π := by
    intro x hx; rw [hTdef] at hx; exact hx.2
  have hTle : T ≤ Lst.map π := fun _ hx => hTL_mem hx
  have hTea : IsElemAbelian q T :=
    ⟨⟨⟨fun x y => Subtype.ext (hE.comm (hTE_mem x.2) (hTE_mem y.2))⟩⟩,
      fun x hx => hE.2 x (hTE_mem hx)⟩
  have hTcent : ∀ t ∈ T, π a * t = t * π a := fun t ht => hE.comm haE (hTE_mem ht)
  have ha1 : a ^ (q ^ 1) = 1 := by simpa using ha
  obtain ⟨D, _hDLst, hDker, hDmap, hDcomm⟩ :=
    exists_sylow_lift_commuting π hLn hq hLC ⟨1, ha1⟩ hTle hTea hTcent
  have hπane : π a ≠ 1 := fun h => hnot (h ▸ (Lst.map π).one_mem)
  have hordπa : orderOf (π a) = q := orderOf_eq_prime (hE.2 (π a) haE) hπane
  have haven : a ≠ 1 := fun h => hπane (by rw [h, map_one])
  have horda : orderOf a = q := orderOf_eq_prime ha haven
  have hDinj : Function.Injective (π.domRestrict D) := by
    intro x y hxy
    have hxy' : π (x : M) = π (y : M) := hxy
    have hmem : (x : M)⁻¹ * (y : M) ∈ D ⊓ π.ker := by
      refine ⟨D.mul_mem (D.inv_mem x.2) y.2, ?_⟩
      change π ((x : M)⁻¹ * (y : M)) = 1
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    rw [hDker] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem))
  have hDel : IsElemAbelian q D := by
    refine ⟨⟨⟨fun x y => hDinj ?_⟩⟩, fun x hx => ?_⟩
    · show (π.domRestrict D) (x * y) = (π.domRestrict D) (y * x)
      change π ((x : M) * (y : M)) = π ((y : M) * (x : M))
      rw [map_mul, map_mul]
      exact hTea.comm (by rw [← hDmap]; exact ⟨x, x.2, rfl⟩)
        (by rw [← hDmap]; exact ⟨y, y.2, rfl⟩)
    · have hxT : π x ∈ T := by rw [← hDmap]; exact ⟨x, hx, rfl⟩
      have hmem : x ^ q ∈ D ⊓ π.ker := by
        refine ⟨D.pow_mem hx q, ?_⟩
        change π (x ^ q) = 1
        rw [map_pow, hTea.2 (π x) hxT]
      rw [hDker] at hmem
      exact Subgroup.mem_bot.mp hmem
  set F : Subgroup M := Subgroup.zpowers a ⊔ D with hFdef
  have haDcomm : ∀ x ∈ Subgroup.zpowers a, ∀ d ∈ D, x * d = d * x := by
    intro x hx d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (show Commute a d from hDcomm d hd).zpow_left i
  have hFel : IsElemAbelian q F :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers ha) hDel haDcomm
  have haF : a ∈ F := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hDnorm : D ≤ Subgroup.normalizer (Subgroup.zpowers a : Set M) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h := haDcomm x hx d hd
      have e : d * x * d⁻¹ = x := by rw [← h]; group
      rwa [e]
    · intro hx
      have hw : Commute (d * x * d⁻¹) d := haDcomm (d * x * d⁻¹) hx d hd
      have e : x = d⁻¹ * (d * x * d⁻¹) * d := by group
      have e2 : d⁻¹ * (d * x * d⁻¹) * d = d * x * d⁻¹ := by
        rw [mul_assoc, hw, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e, e2]; exact hx
  have hFmap : F.map π = E := by
    have hLnorm : π a ∈ Subgroup.normalizer (Lst.map π : Set H) := map_mem_normalizer_map π hLn a
    have hpaE : π a ∈ Subgroup.normalizer (E : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have e : π a * z * (π a)⁻¹ = z := by rw [hE.comm haE hz]; group
        rwa [e]
      · intro hz
        have hw : π a * z * (π a)⁻¹ ∈ E := hz
        have e : (π a)⁻¹ * (π a * z * (π a)⁻¹) * π a = π a * z * (π a)⁻¹ := by
          rw [hE.comm (E.inv_mem haE) hw]; group
        rw [show z = (π a)⁻¹ * (π a * z * (π a)⁻¹) * π a from by group, e]
        exact hw
    have hpaT : π a ∈ Subgroup.normalizer (T : Set H) := by
      rw [hTdef]
      exact Subgroup.inf_normalizer_le_normalizer_inf (H := E) (K := Lst.map π)
        ⟨hpaE, hLnorm⟩
    have hle' : Subgroup.zpowers (π a) ≤ Subgroup.normalizer (Lst.map π : Set H) :=
      Subgroup.zpowers_le.mpr hLnorm
    have hEeq : E = T ⊔ Subgroup.zpowers (π a) := by
      apply le_antisymm
      · intro e he
        have he' : e ∈ ((Lst.map π ⊔ Subgroup.zpowers (π a) : Subgroup H) : Set H) := hEle he
        rw [Subgroup.coe_mul_of_right_le_normalizer_left (Lst.map π)
          (Subgroup.zpowers (π a)) hle'] at he'
        obtain ⟨l, hl, z, hz, hlz⟩ := he'
        have hlE : l ∈ E := by
          have : l = e * z⁻¹ := by rw [← hlz]; group
          rw [this]
          exact E.mul_mem he ((Subgroup.zpowers_le.mpr haE) (Subgroup.inv_mem _ hz))
        have hlT : l ∈ T := by rw [hTdef]; exact ⟨hlE, hl⟩
        rw [← hlz]
        exact mul_mem_sup hlT hz
      · rw [hTdef]
        exact sup_le inf_le_left (Subgroup.zpowers_le.mpr haE)
    rw [hFdef, Subgroup.map_sup, MonoidHom.map_zpowers, hDmap, sup_comm, hEeq]
  have hFker : F ⊓ π.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxF : x ∈ F := hx.1
    have hxker : π x = 1 := hx.2
    have hxdecomp : x ∈ ((Subgroup.zpowers a ⊔ D : Subgroup M) : Set M) := by
      rw [hFdef] at hxF
      exact hxF
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers a) D hDnorm] at hxdecomp
    obtain ⟨y, hy, d, hd, hyd⟩ := hxdecomp
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hπ : (π a) ^ i * π d = 1 := by
      rw [← hyd, map_mul, map_zpow] at hxker
      exact hxker
    have hπa_i : (π a) ^ i = 1 := by
      have hmem : (π a) ^ i ∈ Lst.map π ⊓ Subgroup.zpowers (π a) := by
        refine ⟨?_, Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩⟩
        have h1 : (π a) ^ i = (π d)⁻¹ := mul_eq_one_iff_eq_inv.mp hπ
        rw [h1]
        exact (Lst.map π).inv_mem (hTL_mem (by rw [← hDmap]; exact ⟨d, hd, rfl⟩))
      rw [inf_map_zpowers_eq_bot_of_notMem π hq hnot hordπa] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hd1 : d = 1 := by
      have hmem : d ∈ D ⊓ π.ker := by
        refine ⟨hd, ?_⟩
        change π d = 1
        have h := hπ
        rw [hπa_i, one_mul] at h
        exact h
      rw [hDker] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hai : a ^ i = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, horda]
      rw [← hordπa]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hπa_i
    rw [← hyd, hai, hd1]
    simp
  exact ⟨F, hFel, haF, hFker, hFmap⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
