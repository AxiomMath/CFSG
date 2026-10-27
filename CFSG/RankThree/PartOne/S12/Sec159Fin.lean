module

public import CFSG.RankThree.PartOne.S12.Sec159Hom
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree StrongP
open scoped commutatorElement

namespace Sec159Cfg

theorem commutator_central_left {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (a y : Q) : ⁅z * a, y⁆ = ⁅a, y⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  simp only [commutatorElement_def, mul_inv_rev]
  have : z * a * y * (a⁻¹ * z⁻¹) * y⁻¹ = z * (a * y * a⁻¹) * z⁻¹ * y⁻¹ := by group
  rw [this, ← hz' (a * y * a⁻¹)]
  group

theorem commutator_central_right {Q : Type*} [Group Q] {w : Q} (hw : w ∈ Subgroup.center Q)
    (x b : Q) : ⁅x, w * b⁆ = ⁅x, b⁆ := by
  have hw' := Subgroup.mem_center_iff.1 hw
  simp only [commutatorElement_def, mul_inv_rev]
  have : x * (w * b) * x⁻¹ * (b⁻¹ * w⁻¹) = w * (x * b * x⁻¹ * b⁻¹) * w⁻¹ := by
    rw [← mul_assoc x w b, hw' x]
    group
  rw [this, ← hw' (x * b * x⁻¹ * b⁻¹)]
  group

theorem commutator_central_mul {Q : Type*} [Group Q] {z w : Q} (hz : z ∈ Subgroup.center Q)
    (hw : w ∈ Subgroup.center Q) (a b : Q) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [commutator_central_left hz, commutator_central_right hw]

theorem aut_eq_one_of_central {Q : Type*} [Group Q] [hQ : Group.IsPerfect Q] (φ : MulAut Q)
    (h : ∀ q, φ q * q⁻¹ ∈ Subgroup.center Q) : φ = 1 := by
  have hcomm : ∀ a b : Q, φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    calc φ ⁅a, b⁆ = ⁅φ a, φ b⁆ := map_commutatorElement φ a b
      _ = ⁅(φ a * a⁻¹) * a, (φ b * b⁻¹) * b⁆ := by simp
      _ = ⁅a, b⁆ := commutator_central_mul (h a) (h b) a b
  have hle : commutator Q ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q) :=
    Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
  have htop : MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    exact hle (by rw [hQ.commutator_eq_top]; trivial)
  ext q
  have : q ∈ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q) := htop ▸ Subgroup.mem_top q
  simpa using this

theorem isKGroup_of_surjective {A B : Type} [Group A] [Group B] (hA : CFSG.IsKGroup A) (f : A →* B)
    (hf : Function.Surjective f) : CFSG.IsKGroup B :=
  hA.of_surjective f hf

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {b : M}

noncomputable def sIso (X : Subgroup M) [X.Normal] (θ : Subgroup ↥X) [θ.Characteristic] :
    ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) ≃*
      ↥(X.map (QuotientGroup.mk' (actQ X θ).ker)) := by
  let φ₀ : ↥X →* ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) :=
    (QuotientGroup.mk' (Subgroup.center (↥X ⧸ θ))).comp (QuotientGroup.mk' θ)
  let ψ : ↥X →* ↥(X.map (QuotientGroup.mk' (actQ X θ).ker)) :=
    ((QuotientGroup.mk' (actQ X θ).ker).comp X.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  have hφ₀ : Function.Surjective φ₀ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hψ : Function.Surjective ψ := by
    rintro ⟨s, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ₀.ker = ψ.ker := by
    ext x
    have h1 : x ∈ φ₀.ker ↔ ((x : ↥X) : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) := by
      rw [MonoidHom.mem_ker]
      exact QuotientGroup.eq_one_iff _
    have h2 : x ∈ ψ.ker ↔ (x : M) ∈ (actQ X θ).ker := by
      rw [MonoidHom.mem_ker, Subtype.ext_iff]
      show (QuotientGroup.mk' (actQ X θ).ker (x : M) = 1) ↔ _
      exact QuotientGroup.eq_one_iff _
    rw [h1, h2]
    constructor
    · intro hc
      exact mem_ker_of_mk_mem_center x.2 hc
    · intro hk
      exact mk_mem_center_of_mem_ker x.2 hk
  exact (QuotientGroup.quotientKerEquivOfSurjective φ₀ hφ₀).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

theorem Cfg159.centralizer_eq_bot (h : Cfg159 p X E P N θ b) :
    Subgroup.centralizer
      (((X.map (QuotientGroup.mk' (actQ X θ).ker) : Subgroup (M ⧸ (actQ X θ).ker))) :
        Set (M ⧸ (actQ X θ).ker)) = ⊥ := by
  have : Group.IsPerfect (↥X ⧸ θ) := h.quasi.1
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (actQ X θ).ker y
  rw [Subgroup.mem_bot]
  have hcentral : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ (actQ X θ).ker := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.1 hy (QuotientGroup.mk' (actQ X θ).ker x) ⟨x, hx, rfl⟩
    have h2 : (QuotientGroup.mk' (actQ X θ).ker) (g * x) =
        (QuotientGroup.mk' (actQ X θ).ker) (x * g) := by
      rw [map_mul, map_mul]; exact h1.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at h2
    have : g * x / (x * g) = g * x * g⁻¹ * x⁻¹ := by simp [div_eq_mul_inv, mul_assoc]
    rwa [this] at h2
  have hg : actQ X θ g = 1 := by
    apply aut_eq_one_of_central
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      have hu : ((MulAut.conjNormal g y * y⁻¹ : ↥X) : M) ∈ (actQ X θ).ker := by
        simpa [MulAut.conjNormal_apply] using hcentral y y.2
      exact mk_mem_center_of_mem_ker (MulAut.conjNormal g y * y⁻¹ : ↥X).2 hu
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hg

theorem map_mem_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G}
    {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    f n ∈ Subgroup.normalizer ((A.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn a).1 ha, by simp⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨n⁻¹ * a * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hn) a).1 ha
      simpa using this
    · have h1 : f a = f n * y * (f n)⁻¹ := hay
      rw [map_mul, map_mul, map_inv, h1]
      group

theorem card_range_dvd_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (hker : f.ker ≤ g.ker) : Nat.card g.range ∣ Nat.card f.range := by
  let q : A ⧸ f.ker →* A ⧸ g.ker := QuotientGroup.map f.ker g.ker (MonoidHom.id A) hker
  have hq : Function.Surjective q := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H a => exact ⟨(a : A ⧸ f.ker), rfl⟩
  have h1 := Subgroup.card_dvd_of_surjective hq
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1

theorem orderOf_dvd_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (hker : f.ker ≤ g.ker) (a : A) : orderOf (g a) ∣ orderOf (f a) := by
  apply orderOf_dvd_of_pow_eq_one
  have h1 : a ^ orderOf (f a) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have h2 := hker h1
  rwa [MonoidHom.mem_ker, map_pow] at h2

theorem Cfg159.exists_mem_inf_normalizer (h : Cfg159 p X E P N θ b) {x : M} (hx : x ∈ X)
    (hxn : QuotientGroup.mk' (actQ X θ).ker x ∈
      Subgroup.normalizer ((E.map (QuotientGroup.mk' (actQ X θ).ker) : Subgroup _) : Set _)) :
    ∃ n ∈ X ⊓ Subgroup.normalizer (E : Set M),
      QuotientGroup.mk' (actQ X θ).ker n = QuotientGroup.mk' (actQ X θ).ker x := by
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  set π := QuotientGroup.mk' K with hπ
  have hconj : ∀ r ∈ E, x * r * x⁻¹ ∈ K ⊔ E := by
    intro r hr
    have h1 : π (x * r * x⁻¹) ∈ E.map π := by
      have h3 := (Subgroup.mem_normalizer_iff.1 hxn (π r)).1 ⟨r, hr, rfl⟩
      rw [map_mul, map_mul, map_inv]
      exact h3
    have h2 : x * r * x⁻¹ ∈ (E.map π).comap π := h1
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    rwa [sup_comm]
  obtain ⟨k, hk, hkn⟩ := h.exists_ker_mul_mem_normalizer le_rfl h.bE hconj
  have hksup := h.ker_le_sup hk
  obtain ⟨z, hz, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hksup
  have hwE : w ∈ E := Subgroup.zpowers_le.2 h.bE hw
  refine ⟨z⁻¹ * x, ⟨X.mul_mem (X.inv_mem hz.2) hx, ?_⟩, ?_⟩
  · have h1 : w * ((z * w)⁻¹ * x) ∈ Subgroup.normalizer (E : Set M) :=
      (Subgroup.normalizer (E : Set M)).mul_mem (Subgroup.le_normalizer hwE) hkn
    have h2 : w * ((z * w)⁻¹ * x) = z⁻¹ * x := by group
    rwa [h2] at h1
  · have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz.1
    rw [map_mul, map_inv, hπz]; simp

@[expose] noncomputable def autHom (X E : Subgroup M) [X.Normal] (θ : Subgroup ↥X) [θ.Characteristic] :
    ↥(X ⊓ Subgroup.normalizer (E : Set M)) →*
      MulAut ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) :=
  (E.map (QuotientGroup.mk' (actQ X θ).ker)).normalizerMonoidHom.comp
    (((QuotientGroup.mk' (actQ X θ).ker).comp
      (X ⊓ Subgroup.normalizer (E : Set M)).subtype).codRestrict _
      fun n => map_mem_normalizer_map _ n.2.2)

omit [Finite M] in
theorem autHom_apply_coe (X E : Subgroup M) [X.Normal] (θ : Subgroup ↥X) [θ.Characteristic]
    (n : ↥(X ⊓ Subgroup.normalizer (E : Set M)))
    (y : ↥(E.map (QuotientGroup.mk' (actQ X θ).ker))) :
    ((autHom X E θ n y : ↥(E.map (QuotientGroup.mk' (actQ X θ).ker))) :
      M ⧸ (actQ X θ).ker) =
      QuotientGroup.mk' (actQ X θ).ker (n : M) * y * (QuotientGroup.mk' (actQ X θ).ker (n : M))⁻¹ :=
  rfl

theorem Cfg159.automizer (h : Cfg159 p X E P N θ b) {A₀ : Type} [Group A₀]
    (f : ↥(X ⊓ Subgroup.normalizer (E : Set M)) →* A₀) (hA : Nat.card A₀ ∣ 24)
    (hA' : ∀ a : A₀, orderOf a ≤ 4)
    (hker : ∀ n : ↥(X ⊓ Subgroup.normalizer (E : Set M)), f n = 1 → ∀ e ∈ E, (n : M) * e = e * n) :
    Nat.card ↥(torusImage (E.map (QuotientGroup.mk' (actQ X θ).ker))
      (X.map (QuotientGroup.mk' (actQ X θ).ker))) ∣ 24 ∧
    ∀ g ∈ torusImage (E.map (QuotientGroup.mk' (actQ X θ).ker))
      (X.map (QuotientGroup.mk' (actQ X θ).ker)), orderOf g ≤ 4 := by
  have hFin : Finite A₀ := Nat.finite_of_card_ne_zero (by
    intro h0; rw [h0] at hA; norm_num at hA)
  set K := (actQ X θ).ker with hK
  have hrange : torusImage (E.map (QuotientGroup.mk' K)) (X.map (QuotientGroup.mk' K)) =
      (autHom X E θ).range := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hφ
      obtain ⟨x, hx, hxs⟩ := Subgroup.mem_subgroupOf.1 hs
      have hxn : QuotientGroup.mk' K x ∈ Subgroup.normalizer
          ((E.map (QuotientGroup.mk' K) : Subgroup _) : Set _) := hxs ▸ s.2
      obtain ⟨n, hn, hπn⟩ := h.exists_mem_inf_normalizer hx hxn
      refine ⟨⟨n, hn⟩, ?_⟩
      show (E.map (QuotientGroup.mk' K)).normalizerMonoidHom _ = _
      congr 1
      exact Subtype.ext (hπn.trans hxs)
    · rintro ⟨n, rfl⟩
      refine Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 ⟨n, n.2.1, rfl⟩, rfl⟩
  have hkerle : f.ker ≤ (autHom X E θ).ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    have hc := hker n hn
    ext ⟨y, e, he, rfl⟩
    rw [autHom_apply_coe]
    have : (n : M) * e * (n : M)⁻¹ = e := by rw [hc e he]; group
    simp only [MulAut.one_apply]
    rw [← map_mul, ← map_inv, ← map_mul, this]
  rw [hrange]
  refine ⟨(card_range_dvd_of_ker_le f (autHom X E θ) hkerle).trans
    ((Subgroup.card_subgroup_dvd_card f.range).trans hA), ?_⟩
  rintro _ ⟨n, rfl⟩
  have h1 := orderOf_dvd_of_ker_le f (autHom X E θ) hkerle n
  exact (Nat.le_of_dvd (orderOf_pos _) h1).trans (hA' _)

end Sec159Cfg

end CFSG.RankThree.PartOne
