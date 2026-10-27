module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailScalar
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

section Conj

variable {G : Type*} [Group G]

theorem map_conj_inf_centralizer {Z : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) (x : G) :
    (Z ⊓ Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Z ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y', ⟨hy'Z, hy'x⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg y').mp hy'Z, ?_⟩
    calc g * y' * g⁻¹ * (g * x * g⁻¹) = g * (y' * x) * g⁻¹ := by group
      _ = g * (x * y') * g⁻¹ := by rw [hy'x]
      _ = g * x * g⁻¹ * (g * y' * g⁻¹) := by group
  · rintro ⟨hyZ, hyx⟩
    refine ⟨g⁻¹ * y * g, ⟨?_, ?_⟩, by group⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hyZ
      simpa using this
    · calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyx]
        _ = x * (g⁻¹ * y * g) := by group

theorem mem_normalizer_inf_centralizer {Z : Subgroup G} {g e : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) (he : g * e = e * g) :
    g ∈ Subgroup.normalizer ((Z ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) := by
  have h1 : g * e * g⁻¹ = e := by rw [he, mul_inv_cancel_right]
  have hmap := map_conj_inf_centralizer hg e
  rw [h1] at hmap
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hmap] at hy
    obtain ⟨y', hy', hyy'⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy'
    have : y' = y := by
      have := congrArg (fun t => g⁻¹ * t * g) hyy'
      simpa [mul_assoc] using this
    rwa [← this]

theorem mem_normalizer_map_conj {Y : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hgx : g * x = x * g) :
    g ∈ Subgroup.normalizer ((Y.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  have hxg : x⁻¹ * g * x = g := by rw [mul_assoc, hgx, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    MulAut.conj_symm_apply]
  have e : x⁻¹ * (g * y * g⁻¹) * x = g * (x⁻¹ * y * x) * g⁻¹ := by
    calc x⁻¹ * (g * y * g⁻¹) * x = (x⁻¹ * g * x) * (x⁻¹ * y * x) * (x⁻¹ * g * x)⁻¹ := by group
      _ = g * (x⁻¹ * y * x) * g⁻¹ := by rw [hxg]
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hg _

end Conj

section Commute

variable {G : Type} [Group G] [Finite G]

theorem commute_of_isThreeCentralIn (h415 : Sec4.Item4_15) {L : Subgroup G}
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {A : Subgroup G} (hA : IsPGroup 3 A) {w d : G} (hwL : w ∈ L)
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1) (hdA : d ∈ A) (hdL : d ∈ L)
    (hd1 : d ≠ 1) (hd : IsThreeCentralIn L d) : w * d = d * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAL3 : IsPGroup 3 ↥(A ⊓ L) := hA.to_le inf_le_left
  have hw3' : IsPGroup 3 (Subgroup.zpowers w) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have e : ((g : G)) ^ 3 = 1 := by
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
    simpa using e
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf (Subgroup.zpowers_le.mpr hwA)
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hwL))
  have hT3 : IsPGroup 3 ((A ⊓ L) ⊔ Subgroup.zpowers w : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hAL3 hw3' hwN
  obtain ⟨T, hT⟩ := (hT3.comap_subtype (K := L)).exists_le_sylow
  have hdT : (⟨d, hdL⟩ : ↥L) ∈ (T : Subgroup ↥L) :=
    hT (Subgroup.mem_comap.mpr (le_sup_left (a := A ⊓ L) ⟨hdA, hdL⟩))
  have hwT : (⟨w, hwL⟩ : ↥L) ∈ (T : Subgroup ↥L) :=
    hT (Subgroup.mem_comap.mpr (le_sup_right (b := Subgroup.zpowers w) (Subgroup.mem_zpowers w)))
  have hTnt : Nontrivial (T : Subgroup ↥L) := by
    refine ⟨⟨⟨⟨d, hdL⟩, hdT⟩, 1, fun h => hd1 ?_⟩⟩
    have := congrArg (fun x : (T : Subgroup ↥L) => ((x : ↥L) : G)) h
    simpa using this
  have hZnt : Nontrivial (Subgroup.center (T : Subgroup ↥L)) := T.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (T : Subgroup ↥L))
  set z₀ : G := (((z : (T : Subgroup ↥L)) : ↥L) : G) with hz₀
  have hz₀L : z₀ ∈ L := ((z : (T : Subgroup ↥L)) : ↥L).2
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    apply hz1
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hcomm : ∀ t ∈ (T : Subgroup ↥L), (t : G) * z₀ = z₀ * t := by
    intro t ht
    have := Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩
    exact congrArg (fun x : (T : Subgroup ↥L) => ((x : ↥L) : G)) this
  have hE : IsPGroup 3 ((T : Subgroup ↥L).map L.subtype) := T.isPGroup'.map L.subtype
  have hzd := Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ2 hE (d₁ := z₀)
    (d₂ := d)
    ⟨(z : (T : Subgroup ↥L)), (z : (T : Subgroup ↥L)).2, rfl⟩ ⟨⟨d, hdL⟩, hdT, rfl⟩ hz₀L hdL
    hz₀1 hd1 ⟨T, (z : (T : Subgroup ↥L)).2, fun t ht => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hcomm t ht)⟩ (by
      obtain ⟨hx, S₂, hS₂, hS₂c⟩ := hd
      exact ⟨S₂, hS₂, hS₂c⟩)
  have hwz : Commute w z₀ := hcomm _ hwT
  have hdz : d ∈ Subgroup.zpowers z₀ := hzd ▸ Subgroup.mem_zpowers d
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hdz
  exact (hwz.zpow_right k).eq

end Commute

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem Sec17Std.c_pow_three (h : Sec17Std G A c L Y₀) : c ^ 3 = 1 := by
  have h3 := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
  rw [Nat.card_zpowers] at h3
  rw [← h3]
  exact pow_orderOf_eq_one c

theorem Sec17Std.c_mem (h : Sec17Std G A c L Y₀) : c ∈ A :=
  (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1

theorem Sec17Std.isE27 (h : Sec17Std G A c L Y₀) : IsE27 A :=
  isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE

theorem Sec17Std.le_centralizer_c (h : Sec17Std G A c L Y₀) :
    L ≤ Subgroup.centralizer ({c} : Set G) :=
  le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1

theorem Sec17Std.commute_of_mem (h : Sec17Std G A c L Y₀) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a :=
  congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem Sec17W.isPGroup_Q (h : Sec17W G A c L Y₀ Y₁ S p P w Q) : IsPGroup p Q :=
  (isPiSubgroup_piOf_iff h.p_prime Q).mp h.mem_qStar_G.prop.2

theorem Sec17W.isPiSubgroup_Q (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    IsPiSubgroup (piOf p) Q :=
  h.mem_qStar_G.prop.2

theorem Sec17W.le_normalizer_Q (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    A ≤ Subgroup.normalizer (Q : Set G) :=
  h.mem_qStar_G.prop.1.1.1.2.2

theorem Sec17W.Q_ne_bot (h : Sec17W G A c L Y₀ Y₁ S p P w Q) : Q ≠ ⊥ := by
  intro hQ
  apply h.commutator_not_le_M
  have hP : P = ⊥ := le_bot_iff.mp (hQ ▸ h.le_Q)
  rw [hP, Subgroup.commutator_bot_left]
  exact bot_le

theorem Sec17W.coprime_omegaOneZ (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    Nat.Coprime 3 (Nat.card (omegaOneZ p Q)) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h.isPGroup_Q.to_le (omegaOneZ_le p Q))
  rw [hk]
  refine Nat.Coprime.pow_right k ?_
  rw [Nat.coprime_primes Nat.prime_three h.p_prime]
  exact (h.three_lt_p).ne

theorem Sec17W.w_pow_three (h : Sec17W G A c L Y₀ Y₁ S p P w Q) : w ^ 3 = 1 := by
  rw [← h.orderOf_w]
  exact pow_orderOf_eq_one w

theorem Sec17W.w_commute_c (h : Sec17W G A c L Y₀ Y₁ S p P w Q) : c * w = w * c :=
  (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c h.w_mem.2)).symm

theorem Sec17Data.r_commute_c_and_inverts_d {s d r : G}
    (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r) : c * r = r * c ∧ r * d * r⁻¹ = d⁻¹ := by
  obtain ⟨x, hxA, hxr, hxrd⟩ := h.r_origin
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hxA
  have hxc : Commute x c := (Subgroup.mem_centralizer_iff.mp hxC c h.c_mem).symm
  have hxd : Commute x d := (Subgroup.mem_centralizer_iff.mp hxC d h.d_mem.1).symm
  have hr₀c : Commute (x * r) c :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hxr.1)
  have hrc : Commute r c := by
    have := hxc.inv_left.mul_left hr₀c
    rwa [inv_mul_cancel_left] at this
  refine ⟨hrc.eq.symm, ?_⟩
  have e : r * d * r⁻¹ = x⁻¹ * ((x * r) * d * (x * r)⁻¹) * x := by group
  rw [e, hxrd, mul_assoc, ← hxd.inv_right.eq, inv_mul_cancel_left]

end Data

section End

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_pow_of_data (h415 : Sec4.Item4_15) (h1721 : Item1721) (h1725 : Item1725)
    (h1728 : Item1728Z) {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
    {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G} {s d r : G}
    (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r) :
    ∃ m : ℕ, ∀ z ∈ omegaOneZ p Q, c * z * c⁻¹ = z ^ m := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  set Z := omegaOneZ p Q with hZdef
  have hZab : IsMulCommutative Z := (isElemAbelian_omegaOneZ p Q).1
  have hZQ : Z ≤ Q := omegaOneZ_le p Q
  have hNZ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    normalizer_le_normalizer_omegaOneZ p Q
  have hcA : c ∈ A := h.c_mem
  have hdA : d ∈ A := h.d_mem.1
  have hcd : c * d = d * c := h.commute_of_mem hcA hdA
  obtain ⟨hZeq, -, hXcard⟩ := h1728 G A c L Y₀ Y₁ S p P w Q s d r h
  rw [← hZdef] at hZeq hXcard
  set X := Z ⊓ Subgroup.centralizer ({c * d} : Set G) with hXdef
  have hwc : c * w = w * c := h.w_commute_c
  have hwd : w * d = d * w := commute_of_isThreeCentralIn h415 (h1721 G A c L Y₀ Y₁ S p P
    h.toSec17Y1) h.isE27.isPGroup h.w_mem.2 h.w_mem.1 h.w_pow_three hdA h.d_mem.2 h.d_ne_one
    h.d_threeCentral
  have hwcd : w * (c * d) = (c * d) * w := by
    rw [← mul_assoc, ← hwc, mul_assoc, hwd, ← mul_assoc]
  have hwX : w ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_inf_centralizer (hNZ h.w_normalizes_Q) hwcd
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha =>
    mem_normalizer_inf_centralizer (hNZ (h.le_normalizer_Q ha))
      (by rw [← mul_assoc, h.commute_of_mem ha hcA, mul_assoc, h.commute_of_mem ha hdA,
        ← mul_assoc])
  have hXinv : X ∈ invariantPiSubgroups Q (Subgroup.zpowers w ⊔ A) (piOf p) := by
    refine ⟨inf_le_left.trans hZQ, fun q hq => h.isPiSubgroup_Q q
      (hq.trans (Subgroup.card_dvd_of_le (inf_le_left.trans hZQ))), ?_⟩
    exact sup_le (Subgroup.zpowers_le.mpr hwX) hAX
  have hXab : IsMulCommutative X :=
    ⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
      (hZab.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩
  obtain ⟨hXeq, hXi, hX3⟩ := h1725 G A c L Y₀ Y₁ S p P w Q h.toSec17WQ X hXinv
  set X₃ := X ⊓ yI Y₁ w 3 with hX₃
  have hX₁ := hXi 1 le_rfl (by norm_num)
  have hX₂ := hXi 2 (by norm_num) (by norm_num)
  have hcard₁ : Nat.card (X ⊓ yI Y₁ w 1 : Subgroup G) = p := by
    have h3 := hX3 hXab
    rw [hXcard] at h3
    exact (Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h3).symm
  have hcard₃ : Nat.card X₃ = p := by
    rw [← hcard₁, hX₁, Subgroup.card_map_of_injective (MulAut.conj (w ^ 1)).injective]
  have hcX : c ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_inf_centralizer (hNZ (h.le_normalizer_Q hcA))
      (by rw [mul_assoc c d c, ← hcd])
  have hcY₃ : c ∈ Subgroup.normalizer (yI Y₁ w 3 : Set G) := by
    have hcY₁ : c ∈ Subgroup.normalizer (Y₁ : Set G) := h.mem_y1Star.prop.1.1.1.2 hcA
    exact mem_normalizer_map_conj hcY₁ (by
      show c * w ^ (3 - 1) = w ^ (3 - 1) * c
      exact ((Commute.pow_right (show Commute c w from hwc) (3 - 1))).eq)
  have hcX₃ : c ∈ Subgroup.normalizer (X₃ : Set G) := le_normalizer_inf
    (Subgroup.zpowers_le.mpr hcX) (Subgroup.zpowers_le.mpr hcY₃) (Subgroup.mem_zpowers c)
  obtain ⟨m, hm⟩ := exists_conj_eq_pow_of_card_prime hcard₃ hcX₃
  refine ⟨m, ?_⟩
  have hcw : ∀ i : ℕ, c * w ^ i = w ^ i * c := fun i =>
    (Commute.pow_right (show Commute c w from hwc) i).eq
  have hm₁ : ∀ z ∈ X ⊓ yI Y₁ w 1, c * z * c⁻¹ = z ^ m := by
    rw [hX₁]
    exact conj_eq_pow_map (hcw 1) hm
  have hm₂ : ∀ z ∈ X ⊓ yI Y₁ w 2, c * z * c⁻¹ = z ^ m := by
    rw [hX₂]
    exact conj_eq_pow_map (hcw 2) hm
  have hXZ : X ≤ Z := inf_le_left
  have hmX : ∀ z ∈ X, c * z * c⁻¹ = z ^ m := by
    rw [hXeq]
    refine conj_eq_pow_sup hZab (sup_le (inf_le_left.trans hXZ) (inf_le_left.trans hXZ))
      (inf_le_left.trans hXZ) ?_ hm
    exact conj_eq_pow_sup hZab (inf_le_left.trans hXZ) (inf_le_left.trans hXZ) hm₁ hm₂
  obtain ⟨hrc', hrd⟩ := h.r_commute_c_and_inverts_d
  have hrc : r * c * r⁻¹ = c := by rw [← hrc', mul_inv_cancel_right]
  have hrZ : r ∈ Subgroup.normalizer (Z : Set G) := hNZ h.r_normalizes_Q
  have hswap : X.map (MulAut.conj r).toMonoidHom =
      Z ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) := by
    rw [hXdef, map_conj_inf_centralizer hrZ (c * d)]
    congr 3
    calc r * (c * d) * r⁻¹ = (r * c * r⁻¹) * (r * d * r⁻¹) := by group
      _ = c * d⁻¹ := by rw [hrc, hrd]
  have hmX' : ∀ z ∈ Z ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G), c * z * c⁻¹ = z ^ m := by
    rw [← hswap]
    exact conj_eq_pow_map hrc' hmX
  rw [hZeq]
  exact conj_eq_pow_sup hZab inf_le_left inf_le_left hmX hmX'

end End

section Partial

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_yI_eq_map_conj {X Y₁ : Subgroup G} {w : G} (hw3 : w ^ 3 = 1)
    (hwX : w ∈ Subgroup.normalizer (X : Set G)) {i : ℕ} (hi1 : 1 ≤ i) :
    X ⊓ yI Y₁ w i = (X ⊓ yI Y₁ w 3).map (MulAut.conj (w ^ i)).toMonoidHom := by
  have hwi : w ^ i ∈ Subgroup.normalizer (X : Set G) := Subgroup.pow_mem _ hwX i
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (w ^ i)).injective,
    Late.map_conj_eq_of_mem_normalizer hwi]
  congr 1
  simp only [yI]
  rw [Late.map_conj_map_conj, ← pow_add, show i + (3 - 1) = (i - 1) + 3 by omega, pow_add, hw3,
    mul_one]

theorem card_ne_of_inverts {p : ℕ} [Fact p.Prime] {Z₁ : Subgroup G}
    (hZe : CFSG.Assembly.IsElemAbelian p Z₁) (hZ1 : Z₁ ≠ ⊥) {c s : G} (hc3 : c ^ 3 = 1)
    (hcZ : c ∈ Subgroup.normalizer (Z₁ : Set G))
    (hfix : Z₁ ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    (hsZ : s ∈ Subgroup.normalizer (Z₁ : Set G)) (hsc : s * c * s⁻¹ = c⁻¹) :
    Nat.card Z₁ ≠ p := by
  intro hcard
  obtain ⟨m, hm⟩ := exists_conj_eq_pow_of_card_prime hcard hcZ
  exact hZ1 (eq_bot_of_conj_eq_pow hZe hsZ hsc (sq_ne_one_of_conj_eq_pow hZe hZ1 hc3 hfix hm) hm)

end Partial

end CFSG.RankThree.PartTwo.Sec17
