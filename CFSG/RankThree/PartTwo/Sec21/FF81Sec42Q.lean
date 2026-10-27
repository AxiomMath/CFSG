module

import CFSG.RankThree.PartTwo.Sec21.FF81Sec42A
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42B
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace Q42

variable {G : Type} [Group G] [Finite G]

def cx (x : G) : ↥(Cen x) := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem cx_central (x : G) (c : ↥(Cen x)) : c * cx x = cx x * c :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)

instance (x : G) : (Subgroup.zpowers (cx x)).Normal :=
  zpowers_normal_of_central (cx x) (cx_central x)

abbrev Q (x : G) : Type := ↥(Cen x) ⧸ Subgroup.zpowers (cx x)

abbrev π (x : G) : ↥(Cen x) →* Q x := QuotientGroup.mk' (Subgroup.zpowers (cx x))

theorem π_surj (x : G) (y : Q x) : ∃ u : ↥(Cen x), π x u = y :=
  QuotientGroup.mk'_surjective _ y

theorem π_eq_one_iff {x : G} (u : ↥(Cen x)) : π x u = 1 ↔ ∃ k : ℤ, (u : G) = x ^ k := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [hk]; rfl)⟩

theorem π_cx (x : G) : π x (cx x) = 1 := (π_eq_one_iff _).mpr ⟨1, by rw [zpow_one]; rfl⟩

theorem π_eq_iff {x : G} (u v : ↥(Cen x)) : π x u = π x v ↔ ∃ k : ℤ, (v : G) = u * x ^ k := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : x ^ k = (u : G)⁻¹ * v := by simpa [cx] using congrArg Subtype.val hk
    rw [h]; group
  · rintro ⟨k, hk⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [cx, SubgroupClass.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hk]; group

theorem lift_conj {x : G} {u v w : ↥(Cen x)}
    (h : π x u * π x v * (π x u)⁻¹ ∈ Subgroup.zpowers (π x w)) :
    ∃ k j : ℤ, (u : G) * v * (u : G)⁻¹ = (w : G) ^ k * x ^ j := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← map_zpow, ← map_mul, ← map_inv, ← map_mul, π_eq_iff] at hk
  obtain ⟨j, hj⟩ := hk
  exact ⟨k, j, by simpa using hj⟩

theorem π_mem_zpowers_of_mem_closure {x : G} {y w : ↥(Cen x)}
    (h : (y : G) ∈ Subgroup.closure {(w : G), x}) : π x y ∈ Subgroup.zpowers (π x w) := by
  set P : Subgroup ↥(Cen x) := (Subgroup.zpowers (π x w)).comap (π x)
  have hle : Subgroup.closure {(w : G), x} ≤ P.map (Cen x).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy) <;> rw [hy]
    · exact ⟨w, Subgroup.mem_zpowers _, rfl⟩
    · refine ⟨cx x, ?_, rfl⟩
      show π x (cx x) ∈ Subgroup.zpowers (π x w)
      rw [π_cx]; exact Subgroup.one_mem _
  obtain ⟨p, hp, hpy⟩ := hle h
  have : p = y := Subtype.ext hpy
  rw [← this]; exact hp

theorem mem_nor_zpowers {X : Type} [Group X] [Finite X] {g y : X}
    (h : g * y * g⁻¹ ∈ Subgroup.zpowers y) : g ∈ Nor (Subgroup.zpowers y) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  exact (Subgroup.zpowers_le.mpr h) (conj_mem_zpowers rfl hz)

theorem mem_nor_of_mem_cen {X : Type} [Group X] [Finite X] {g y : X} (h : g ∈ Cen y) :
    g ∈ Nor (Subgroup.zpowers y) :=
  mem_nor_zpowers (by rw [conj_of_mem_cen h]; exact Subgroup.mem_zpowers y)

theorem mem_cen_of_commute {X : Type} [Group X] {g y : X} (h : g * y = y * g) : g ∈ Cen y :=
  Subgroup.mem_centralizer_singleton_iff.mpr h

theorem closure_pair_inv (a c : G) :
    Subgroup.closure ({a, c⁻¹} : Set G) = Subgroup.closure {a, c} := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro y (hy | hy) <;> rw [hy]
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · rintro y (hy | hy) <;> rw [hy]
    · exact Subgroup.subset_closure (by simp)
    · rw [← inv_inv c]; exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem conjBy_closure_pair (g a c : G) :
    conjBy g (Subgroup.closure ({a, c} : Set G)) =
      Subgroup.closure {g * a * g⁻¹, g * c * g⁻¹} := by
  rw [conjBy, MonoidHom.map_closure, Set.image_pair]; rfl

@[expose] def Conc (x : G) (E : Subgroup G) : Prop :=
  Odd (Nat.card (Opp 3 (Cen x))) ∧ setMul (Opp 3 (Cen x)) (Cen x ⊓ Nor E) = Cen x

theorem nor_conjBy (g : G) (E : Subgroup G) : Nor (conjBy g E) = conjBy g (Nor E) := by
  ext y
  rw [mem_conjBy_iff]
  constructor
  · intro h
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have : g * r * g⁻¹ ∈ conjBy g E := ⟨r, hr, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp h _).mp this
    rw [mem_conjBy_iff] at h2
    rw [SetLike.mem_coe]
    convert h2 using 1; group
  · intro h
    exact mem_nor_conjBy fun u hu => (Subgroup.mem_normalizer_iff.mp h u).mp hu

theorem conc_conj {x : G} {E : Subgroup G} (h : Conc x E) (g : G) :
    Conc (g * x * g⁻¹) (conjBy g E) := by
  have hC : Cen (g * x * g⁻¹) = conjBy g (Cen x) := cen_conj g x
  have hO : Opp 3 (Cen (g * x * g⁻¹)) = conjBy g (Opp 3 (Cen x)) := by
    rw [hC, conjBy_opp]
  refine ⟨by rw [hO, card_conjBy]; exact h.1, ?_⟩
  ext z
  constructor
  · rintro ⟨o, ho, n, hn, rfl⟩
    exact (Cen _).mul_mem (opp_le _ ho) hn.1
  · intro hz
    rw [SetLike.mem_coe, hC, mem_conjBy_iff, ← SetLike.mem_coe, ← h.2] at hz
    obtain ⟨o, ho, n, hn, hon⟩ := hz
    refine ⟨g * o * g⁻¹, ?_, g * n * g⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [hO]; exact ⟨o, ho, rfl⟩
    · rw [hC]; exact ⟨n, hn.1, rfl⟩
    · rw [nor_conjBy]; exact ⟨n, hn.2, rfl⟩
    · calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = _ := by rw [hon]; group

noncomputable def qq (x g : G) : Q x := by
  classical exact if h : g ∈ Cen x then π x ⟨g, h⟩ else 1

theorem qq_eq {x g : G} (h : g ∈ Cen x) : qq x g = π x ⟨g, h⟩ := by
  classical exact dif_pos h

theorem qq_surj (x : G) (y : Q x) : ∃ g ∈ Cen x, qq x g = y := by
  obtain ⟨u, rfl⟩ := π_surj x y
  exact ⟨u, u.2, qq_eq u.2⟩

theorem qq_mul {x g h : G} (hg : g ∈ Cen x) (hh : h ∈ Cen x) :
    qq x (g * h) = qq x g * qq x h := by
  rw [qq_eq hg, qq_eq hh, qq_eq ((Cen x).mul_mem hg hh), ← map_mul]; rfl

theorem qq_inv {x g : G} (hg : g ∈ Cen x) : qq x g⁻¹ = (qq x g)⁻¹ := by
  rw [qq_eq hg, qq_eq ((Cen x).inv_mem hg), ← map_inv]; rfl

theorem qq_one (x : G) : qq x 1 = 1 := by
  rw [qq_eq (Cen x).one_mem]; exact map_one _

theorem qq_pow {x g : G} (hg : g ∈ Cen x) (n : ℕ) : qq x (g ^ n) = qq x g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, qq_one]
  | succ n ih => rw [pow_succ, qq_mul ((Cen x).pow_mem hg n) hg, ih, pow_succ]

theorem qq_zpow {x g : G} (hg : g ∈ Cen x) (n : ℤ) : qq x (g ^ n) = qq x g ^ n := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, qq_pow hg]
  · rw [zpow_negSucc, zpow_negSucc, qq_inv ((Cen x).pow_mem hg _), qq_pow hg]

theorem qq_conj {x g h : G} (hg : g ∈ Cen x) (hh : h ∈ Cen x) :
    qq x (g * h * g⁻¹) = qq x g * qq x h * (qq x g)⁻¹ := by
  rw [qq_mul ((Cen x).mul_mem hg hh) ((Cen x).inv_mem hg), qq_mul hg hh, qq_inv hg]

theorem qq_eq_one_iff {x g : G} (hg : g ∈ Cen x) : qq x g = 1 ↔ ∃ k : ℤ, g = x ^ k := by
  rw [qq_eq hg, π_eq_one_iff]

theorem qq_xpow (x : G) (k : ℤ) : qq x (x ^ k) = 1 :=
  (qq_eq_one_iff ((Cen x).zpow_mem (cx x).2 k)).mpr ⟨k, rfl⟩

theorem mem_cen_mul {a c g : G} (ha : g ∈ Cen a) (hc : g ∈ Cen c) : g ∈ Cen (a * c) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hc ⊢
  rw [← mul_assoc, ha, mul_assoc, hc, mul_assoc]

theorem lift_conj' {x g v w : G} (hg : g ∈ Cen x) (hv : v ∈ Cen x) (hw : w ∈ Cen x)
    (h : qq x g * qq x v * (qq x g)⁻¹ ∈ Subgroup.zpowers (qq x w)) :
    ∃ k j : ℤ, g * v * g⁻¹ = w ^ k * x ^ j := by
  rw [qq_eq hg, qq_eq hv, qq_eq hw] at h
  exact lift_conj (u := ⟨g, hg⟩) (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) h

theorem lift_nor' {x g v : G} (hg : g ∈ Cen x) (hv : v ∈ Cen x)
    (h : qq x g ∈ Nor (Subgroup.zpowers (qq x v))) :
    ∃ k j : ℤ, g * v * g⁻¹ = v ^ k * x ^ j :=
  lift_conj' hg hv hv ((Subgroup.mem_normalizer_iff.mp h _).mp (Subgroup.mem_zpowers _))

theorem qq_mem_zpowers {x y w : G} (hy : y ∈ Cen x) (hw : w ∈ Cen x)
    (h : y ∈ Subgroup.closure {w, x}) : qq x y ∈ Subgroup.zpowers (qq x w) := by
  rw [qq_eq hy, qq_eq hw]
  exact π_mem_zpowers_of_mem_closure (y := ⟨y, hy⟩) (w := ⟨w, hw⟩) h

theorem nor_of' {x g v : G} (hg : g ∈ Cen x) (hv : v ∈ Cen x)
    (h : g * v * g⁻¹ ∈ Subgroup.closure {v, x}) : qq x g ∈ Nor (Subgroup.zpowers (qq x v)) := by
  refine mem_nor_zpowers ?_
  have hc : g * v * g⁻¹ ∈ Cen x := (Cen x).mul_mem ((Cen x).mul_mem hg hv) ((Cen x).inv_mem hg)
  rw [← qq_conj hg hv]
  exact qq_mem_zpowers hc hv h

theorem qq_mem_cen {x g h : G} (hg : g ∈ Cen x) (hh : h ∈ Cen x) (hc : g * h = h * g) :
    qq x g ∈ Cen (qq x h) :=
  mem_cen_of_commute (by rw [← qq_mul hg hh, ← qq_mul hh hg, hc])

@[expose] def img (x : G) (K : Subgroup G) : Subgroup (Q x) := (K.subgroupOf (Cen x)).map (π x)

theorem mem_img {x : G} {K : Subgroup G} {y : Q x} :
    y ∈ img x K ↔ ∃ g ∈ K, g ∈ Cen x ∧ qq x g = y := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, u.2, qq_eq u.2⟩
  · rintro ⟨g, hgK, hg, rfl⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgK, (qq_eq hg).symm⟩

theorem qq_mem_img {x g : G} {K : Subgroup G} (hgK : g ∈ K) (hg : g ∈ Cen x) :
    qq x g ∈ img x K := mem_img.mpr ⟨g, hgK, hg, rfl⟩

theorem img_closure {x : G} {S : Set G} (hS : S ⊆ Cen x) :
    img x (Subgroup.closure S) = Subgroup.closure (qq x '' S) := by
  have hle : Subgroup.closure S ≤ Cen x := (Subgroup.closure_le _).mpr hS
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
  · intro y hy
    obtain ⟨g, hgS, -, rfl⟩ := mem_img.mp hy
    clear hy
    induction hgS using Subgroup.closure_induction with
    | mem z hz => exact Subgroup.subset_closure ⟨z, hz, rfl⟩
    | one => rw [qq_one]; exact Subgroup.one_mem _
    | mul a c ha hc iha ihc =>
        rw [qq_mul (hle ha) (hle hc)]; exact Subgroup.mul_mem _ iha ihc
    | inv a ha iha => rw [qq_inv (hle ha)]; exact Subgroup.inv_mem _ iha
  · rintro _ ⟨g, hg, rfl⟩
    exact qq_mem_img (Subgroup.subset_closure hg) (hS hg)

theorem card_subgroupOf_dvd (K H : Subgroup G) : Nat.card (K.subgroupOf H) ∣ Nat.card K := by
  have h1 : Nat.card ((K.subgroupOf H).map H.subtype) = Nat.card (K.subgroupOf H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [← h1, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem coprime_card_img {x : G} {K : Subgroup G} (h : Nat.Coprime 3 (Nat.card K)) :
    Nat.Coprime 3 (Nat.card (img x K)) :=
  Nat.Coprime.coprime_dvd_right ((Subgroup.card_map_dvd _ _).trans (card_subgroupOf_dvd _ _)) h

theorem img_equiv {x : G} {K : Subgroup G} (hK : K ≤ Cen x)
    (hinj : ∀ k ∈ K, (∃ i : ℤ, k = x ^ i) → k = 1) : Nonempty (↥(img x K) ≃* ↥K) := by
  set f : ↥K →* Q x := (π x).comp (Subgroup.inclusion hK)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : π x ⟨k, hK k.2⟩ = 1 := hk
    rw [π_eq_one_iff] at h1
    exact Subtype.ext (hinj k k.2 h1)
  have hr : f.range = img x K := by
    ext y
    rw [MonoidHom.mem_range, mem_img]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, hK k.2, qq_eq (hK k.2)⟩
    · rintro ⟨g, hgK, hg, rfl⟩
      exact ⟨⟨g, hgK⟩, (qq_eq hg).symm⟩
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hf).symm⟩

theorem orderOf_conj' {X : Type} [Group X] (g k : X) : orderOf (g * k * g⁻¹) = orderOf k :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective k

theorem lift_opp {x : G} (hx3 : x ^ 3 = 1) (R : Subgroup (Q x))
    (hR : Nat.Coprime 3 (Nat.card R)) :
    ∃ K : Subgroup G, K ≤ Cen x ∧ Nat.Coprime 3 (Nat.card K) ∧ (∀ g ∈ K, qq x g ∈ R) ∧
      (∀ g ∈ Cen x, qq x g ∈ R → ∃ k ∈ K, ∃ i : ℤ, g = k * x ^ i) ∧
      (∀ g ∈ Cen x, qq x g ∈ R → Nat.Coprime 3 (orderOf g) → g ∈ K) := by
  have hc3 : cx x ^ 3 = 1 := Subtype.ext (by simpa [cx] using hx3)
  obtain ⟨K₀, hK₀, h2, h3, h4⟩ := exists_hall_of_central (cx_central x) hc3 R hR
  refine ⟨K₀.map (Cen x).subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective (Cen x).subtype_injective]
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.coe_subtype, qq_eq k.2]
    exact h2 k hk
  · intro g hg hgR
    rw [qq_eq hg] at hgR
    obtain ⟨k, hk, z, hz, hkz⟩ := h3 ⟨g, hg⟩ hgR
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, ⟨k, hk, rfl⟩, i, ?_⟩
    have := congrArg Subtype.val hkz
    simpa [cx] using this
  · intro g hg hgR hco
    rw [qq_eq hg] at hgR
    refine ⟨⟨g, hg⟩, h4 ⟨g, hg⟩ hgR ?_, rfl⟩
    rwa [← Subgroup.orderOf_coe]

end Q42

end CFSG.RankThree.PartTwo.Sec21.FF81
