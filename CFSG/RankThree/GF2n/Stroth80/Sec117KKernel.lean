module

public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec119KU
import CFSG.RankThree.GF2n.Stroth80.Sec119Lift
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
import CFSG.ClassicalGroups.Unitary.ThreeEven

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

omit [Finite G] in
private theorem commutatorElement_mul_left_eq (k₁ k₂ x : G) :
    ⁅k₁ * k₂, x⁆ = k₁ * ⁅k₂, x⁆ * k₁⁻¹ * ⁅k₁, x⁆ := by
  simp only [commutatorElement_def]
  group

omit [Finite G] in
private theorem commutatorElement_inv_left_eq (k x : G) :
    ⁅k⁻¹, x⁆ = k⁻¹ * ⁅k, x⁆⁻¹ * k := by
  simp only [commutatorElement_def]
  group

def Ctx.a2PlaneKernel (hc : Ctx M Q Z B) (a : G) : Subgroup ↥(Xbar M Q Z B) where
  carrier := {c | (c : Mbar M Q) ∈ fixA2Plane M Q Z a}
  mul_mem' := by
    rintro c d ⟨k₁, hk₁, hk₁a, hk₁x⟩ ⟨k₂, hk₂, hk₂a, hk₂x⟩
    refine ⟨k₁ * k₂, by rw [map_mul, hk₁, hk₂]; rfl, ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_mul, commutatorElement_mul_left_eq]
      exact Q.mul_mem ((hc.conj_mem_Q_of_mem_M (H0_le_M k₁.2)).1 _ hk₂a) hk₁a
    · rw [Subgroup.coe_mul, commutatorElement_mul_left_eq]
      have hz := hk₂x x hx
      have h1 : (k₁ : G) * ⁅(k₂ : G), x⁆ * (k₁ : G)⁻¹ = ⁅(k₂ : G), x⁆ := by
        rw [← Subgroup.mem_centralizer_iff.mp k₁.2.2 _ hz, mul_inv_cancel_right]
      rw [h1]
      exact Z.mul_mem hz (hk₁x x hx)
  one_mem' := ⟨1, map_one _, by simp [Q.one_mem], fun x _ => by simp [Z.one_mem]⟩
  inv_mem' := by
    rintro c ⟨k, hk, hka, hkx⟩
    refine ⟨k⁻¹, by rw [map_inv, hk]; rfl, ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_inv, commutatorElement_inv_left_eq]
      exact (hc.conj_mem_Q_of_mem_M (H0_le_M k.2)).2 _ (Q.inv_mem hka)
    · rw [Subgroup.coe_inv, commutatorElement_inv_left_eq]
      have hz := hkx x hx
      have hcomm : Commute ⁅(k : G), x⁆ (k : G) := Subgroup.mem_centralizer_iff.mp k.2.2 _ hz
      rw [mul_assoc, hcomm.inv_left.eq, inv_mul_cancel_left]
      exact Z.inv_mem hz

theorem Ctx.mem_a2PlaneKernel_iff (hc : Ctx M Q Z B) {a : G} {c : ↥(Xbar M Q Z B)} :
    c ∈ hc.a2PlaneKernel a ↔ (c : Mbar M Q) ∈ fixA2Plane M Q Z a :=
  Iff.rfl

theorem Ctx.commute_of_mem_a2PlaneKernel (hc : Ctx M Q Z B) {a : G} (haM : a ∈ M)
    {t : ↥(Xbar M Q Z B)} (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, haM⟩ : ↥M))
    {c : ↥(Xbar M Q Z B)} (hcK : c ∈ hc.a2PlaneKernel a) : t * c = c * t := by
  obtain ⟨k, hk, hka, -⟩ := hcK
  have h1 := (mk_commute_iff ⟨(k : G), H0_le_M k.2⟩ ⟨a, haM⟩).mpr hka
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ht, ← hk]
  exact h1.eq.symm

theorem Ctx.xbarAct_eq_self_of_mem_a2PlaneKernel (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {a : G} (haH : a ∈ H0 M Z)
    {c : ↥(Xbar M Q Z B)} (hcK : c ∈ hc.a2PlaneKernel a) {u : M₀.E}
    (hu : u ∈ LinearMap.range ((φ ⟨a, haH⟩ : M₀.E →ₗ[K] M₀.E) - 1)) :
    xbarAct hc φ hφker c u = u := by
  obtain ⟨k, hk, -, hkx⟩ := hcK
  obtain ⟨haQ, haQ'⟩ := hc.conj_mem_Q_of_mem_M (H0_le_M haH)
  obtain ⟨x, hx, hxQ, rfl⟩ := (Tim79.QuadModel.mem_img_commutator_zpowers (φ ⟨a, haH⟩) haQ
    haQ' (fun y hy => hφπ ⟨a, haH⟩ y hy)).mpr hu
  have hkx' : (k : G) * x * (k : G)⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M (H0_le_M k.2)).1 x hxQ
  rw [xbarAct_apply, ← hk, liftF_mkH hφker, ← hφπ k x hxQ]
  exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ hkx').mp (hkx x hx)

theorem Ctx.conj_mem_a2PlaneKernel (hc : Ctx M Q Z B) {a : G} (haH : a ∈ H0 M Z)
    {t : ↥(Xbar M Q Z B)} (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, H0_le_M haH⟩ : ↥M))
    {g h : ↥(Xbar M Q Z B)} (hg : t * g = g * t) (hh : h ∈ hc.a2PlaneKernel a) :
    g * h * g⁻¹ ∈ hc.a2PlaneKernel a := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hD
  have hT : xbarAct hc φ hφker t = φ ⟨a, haH⟩ := by
    rw [xbarAct_apply, ht]
    exact liftF_mkH hφker ⟨a, haH⟩
  have hht : t * h = h * t := hc.commute_of_mem_a2PlaneKernel (H0_le_M haH) ht hh
  have hginv : t * g⁻¹ = g⁻¹ * t := by
    calc t * g⁻¹ = g⁻¹ * (g * t) * g⁻¹ := by group
      _ = g⁻¹ * (t * g) * g⁻¹ := by rw [hg]
      _ = g⁻¹ * t := by group
  have hconj : t * (g * h * g⁻¹) = g * h * g⁻¹ * t := by
    calc t * (g * h * g⁻¹) = (t * g) * h * g⁻¹ := by group
      _ = g * (t * h) * g⁻¹ := by rw [hg]; group
      _ = g * h * (t * g⁻¹) := by rw [hht]; group
      _ = g * h * g⁻¹ * t := by rw [hginv]; group
  have hca : ((g * h * g⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) *
      QuotientGroup.mk (⟨a, H0_le_M haH⟩ : ↥M) =
      QuotientGroup.mk (⟨a, H0_le_M haH⟩ : ↥M) * ((g * h * g⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) := by
    rw [← ht]
    exact (congrArg Subtype.val hconj).symm
  refine hc.mem_fixA2Plane_of_liftF_fix hφπ hφker haH (hc.Xbar_le_bar_H0 (g * h * g⁻¹).2) hca
    fun u hu => ?_
  have hu' := xbarAct_mem_range hc hφker hT hginv hu
  have h1 := hc.xbarAct_eq_self_of_mem_a2PlaneKernel hφπ hφker haH hh hu'
  rw [← xbarAct_apply hc φ hφker, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    h1, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

omit [(Q.subgroupOf M).Normal] in
theorem Ctx.comm_mem_Z_of_mem_fixA2Plane (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) {k : ↥(H0 M Z)}
    (hk : ∀ x ∈ ⁅Q, Subgroup.zpowers a⁆, ⁅(k : G), x⁆ ∈ Z) {β : G} (hβ : β ∈ B) :
    ⁅(k : G), β⁆ ∈ Z := by
  let H : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (Z : Set G) ∧ ⁅(k : G), x⁆ ∈ Z}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
        rw [show ⁅(k : G), x * y⁆ = ⁅(k : G), x⁆ * (x * ⁅(k : G), y⁆ * x⁻¹) by
          simp only [commutatorElement_def]; group]
        exact Z.mul_mem hx.2 ((Subgroup.mem_normalizer_iff.mp hx.1 _).mp hy.2)⟩
      one_mem' := ⟨Subgroup.one_mem _, by simp [Z.one_mem]⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
        rw [show ⁅(k : G), x⁻¹⁆ = x⁻¹ * ⁅(k : G), x⁆⁻¹ * x⁻¹⁻¹ by
          simp only [commutatorElement_def]; group]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx.1) _).mp
          (Z.inv_mem hx.2)⟩ }
  have hQa : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hc.comm_mem_Q (M.zpow_mem (hc.LB_le_M ha) n) hx
  have hle : ⁅Q, Subgroup.zpowers a⁆ ⊔ Z ≤ H := by
    refine sup_le (fun x hx => ⟨hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hQa hx)), hk x hx⟩)
      (fun z hz => ⟨Subgroup.le_normalizer hz, ?_⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp k.2.2 z hz).symm]
    exact Z.one_mem
  exact (hle (hc.B_le_commutator_of_a2 ha hA hβ)).2

theorem Ctx.mem_normalizer_bar_LB_of_mem_a2PlaneKernel (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {h : ↥(Xbar M Q Z B)}
    (hh : h ∈ hc.a2PlaneKernel a) :
    (h : Mbar M Q) ∈ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  obtain ⟨k, hk, -, hkx⟩ := hh
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, -, -, hB, -, -⟩ := hc.dictB hD
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp hD
  obtain ⟨β, hβB, hβQ, hβb⟩ := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  have hkβ : (k : G) * β * (k : G)⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M (H0_le_M k.2)).1 β hβQ
  have hfix : (φ k : M₀.E →ₗ[K] M₀.E) b = (1 : K) • b := by
    rw [one_smul, ← hβb]
    show φ k (M₀.π β) = M₀.π β
    rw [← hφπ k β hβQ]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hβQ hkβ).mp
      (hc.comm_mem_Z_of_mem_fixA2Plane ha hA hkx hβB)
  rw [← hk]
  exact hc.mk_mem_normalizer_bar_LB_of_fix_line hB (H0_le_M k.2)
    (T := (φ k : M₀.E →ₗ[K] M₀.E)) (fun y hy => hφπ k y hy) hfix

private theorem Ctx.sq_eq_one_of_coe_eq_mk (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M)) : t ^ 2 = 1 := by
  have h2 : orderOf (t : Mbar M Q) = 2 := by
    rw [ht]
    exact Ctx.orderOf_eq_two_of_mem_Ebar (hc.mk_mem_Ebar ha hA)
  rw [Subgroup.orderOf_coe] at h2
  rw [← h2]
  exact pow_orderOf_eq_one t

omit [Finite G] in
private theorem card_dvd_of_ker_le_ker {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C) (h : g.ker ≤ f.ker) :
    Nat.card B ∣ Nat.card C := by
  have h2 : Nat.card (A ⧸ g.ker) ∣ Nat.card C := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact (Subgroup.card_dvd_of_surjective
    (hf := QuotientGroup.lift_surjective_of_surjective g.ker f hf h)).trans h2

omit [Finite G] in
private theorem card_dvd_of_forall_mem_ker_eq_one {A B C : Type*} [Group A] [Group B] [Group C]
    {π : A →* B} (hπ : Function.Surjective π) {L : Subgroup B} (ρ : ↥(L.comap π) →* C)
    (hρ : ∀ g ∈ ρ.ker, π (g : A) = 1) : Nat.card L ∣ Nat.card C := by
  refine card_dvd_of_ker_le_ker ((π.comp (L.comap π).subtype).codRestrict L fun g => g.2) ?_ ρ
    fun g hg => MonoidHom.mem_ker.mpr (Subtype.ext (hρ g hg))
  rintro ⟨l, hl⟩
  obtain ⟨x, rfl⟩ := hπ l
  exact ⟨⟨x, hl⟩, rfl⟩

private theorem card_generalLinearGroup_eq_card_GL_finrank (K W : Type) [Field K]
    [AddCommGroup W] [Module K W] [Module.Finite K W] :
    Nat.card (LinearMap.GeneralLinearGroup K W) =
      Nat.card (GL (Fin (Module.finrank K W)) K) :=
  Nat.card_congr (Units.mapEquiv
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K W)).toRingEquiv.toMulEquiv).toEquiv

private theorem card_GL_fin_two_eq {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) :
    Nat.card (GL (Fin 2) K) = 2 ^ a * (2 ^ a - 1) * (2 ^ (2 * a) - 1) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK, Fin.prod_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, ← pow_mul, Nat.mul_comm a 2]
  have h2 : 2 ^ (2 * a) - 2 ^ a = 2 ^ a * (2 ^ a - 1) := by
    rw [Nat.mul_sub_one, two_mul, pow_add]
  rw [h2]
  exact Nat.mul_comm _ _

private theorem Ctx.mem_a2PlaneKernel_of_xbarAct_eq_self (hc : Ctx M Q Z B) {K : Type}
    [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {a : G} (haH : a ∈ H0 M Z)
    {t : ↥(Xbar M Q Z B)} (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, H0_le_M haH⟩ : ↥M))
    {g : ↥(Xbar M Q Z B)} (hg : t * g = g * t)
    (hfix : ∀ u ∈ LinearMap.range ((φ ⟨a, haH⟩ : M₀.E →ₗ[K] M₀.E) - 1),
      xbarAct hc φ hφker g u = u) :
    g ∈ hc.a2PlaneKernel a := by
  refine hc.mem_fixA2Plane_of_liftF_fix hφπ hφker haH (hc.Xbar_le_bar_H0 g.2) ?_ fun u hu => ?_
  · rw [← ht]
    exact (congrArg Subtype.val hg).symm
  · rw [← xbarAct_apply hc φ hφker]
    exact hfix u hu

private theorem Ctx.card_dvd_of_inf_map_a2PlaneKernel_eq_bot (hc : Ctx M Q Z B) {a' : ℕ}
    (ha' : Nat.card Z = 2 ^ a') {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a)
    {t : ↥(Xbar M Q Z B)} (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M))
    {L : Subgroup (XbarMod M Q Z B)} (hLt : L ≤ Subgroup.centralizer {(t : XbarMod M Q Z B)})
    (hLN : L ⊓ (hc.a2PlaneKernel a).map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))) =
      ⊥) :
    Nat.card L ∣ 2 ^ a' * (2 ^ a' - 1) * (2 ^ (2 * a') - 1) := by
  obtain ⟨n, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hD
  have haH : a ∈ H0 M Z := hc.LB_le_H0 ha
  have hK : 1 < Nat.card (GaloisField 2 n) := by
    have := hc.hyp.q4
    rw [hD.card]
    omega
  obtain ⟨haQ, haQ'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M ha)
  have hdim := ((isA2_iff M₀ hD.reg hD.card hK (φ ⟨a, haH⟩) haQ haQ'
    (fun x hx => hφπ ⟨a, haH⟩ x hx)).mp hA).2.2.1
  have hT : xbarAct hc φ hφker t = φ ⟨a, haH⟩ := by
    rw [xbarAct_apply, ht]
    exact liftF_mkH hφker ⟨a, haH⟩
  set pr := QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) with hpr
  have hcomm : ∀ g : ↥(L.comap pr), t * g = g * t := fun g =>
    (commute_of_mk_commute_of_odd_center hc.odd_card_center_Xbar
      (hc.sq_eq_one_of_coe_eq_mk ha hA ht)
      (Subgroup.mem_centralizer_singleton_iff.mp (hLt (Subgroup.mem_comap.mp g.2)))).symm
  obtain ⟨ρ, hρ⟩ := CFSG.ClassicalGroups.Unitary.exists_hom_generalLinearGroup_restrict
    ((xbarAct hc φ hφker).comp (L.comap pr).subtype)
    (LinearMap.range ((φ ⟨a, haH⟩ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1))
    fun g _ hw => xbarAct_mem_range hc hφker hT (hcomm g) hw
  have h1 := card_dvd_of_forall_mem_ker_eq_one (QuotientGroup.mk'_surjective _) ρ fun g hg => by
    have hgK := hc.mem_a2PlaneKernel_of_xbarAct_eq_self hφπ hφker haH ht (hcomm g)
      fun u hu => by simpa [MonoidHom.mem_ker.mp hg] using (hρ g ⟨u, hu⟩).symm
    have hmem : pr (g : ↥(Xbar M Q Z B)) ∈ L ⊓ (hc.a2PlaneKernel a).map pr :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp g.2, Subgroup.mem_map_of_mem pr hgK⟩
    rwa [hLN, Subgroup.mem_bot] at hmem
  rwa [card_generalLinearGroup_eq_card_GL_finrank, hdim,
    card_GL_fin_two_eq (hD.card.trans ha')] at h1

theorem Ctx.isA2PlaneKernel_mk (hc : Ctx M Q Z B) {a' : ℕ} (ha' : Nat.card Z = 2 ^ a') {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M)) :
    IsA2PlaneKernel (t : XbarMod M Q Z B) a'
      ((hc.a2PlaneKernel a).map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)))) where
  le_centralizer := by
    rintro _ ⟨c, hcK, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, (hc.commute_of_mem_a2PlaneKernel (hc.LB_le_M ha) ht hcK).symm]
  conj_mem c hct := by
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hgt := commute_of_mk_commute_of_odd_center hc.odd_card_center_Xbar
      (hc.sq_eq_one_of_coe_eq_mk ha hA ht) (Subgroup.mem_centralizer_singleton_iff.mp hct)
    refine ⟨g * h * g⁻¹, hc.conj_mem_a2PlaneKernel (hc.LB_le_H0 ha) ht hgt.symm hh, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  radical S P R hS hPS hPt hRP hRn hR := by
    obtain ⟨S', P', R', hS', hPS', hP'P, hR'R, hP't, hR'P', hR'n, hR'⟩ :=
      exists_lift_radical_of_odd_center hc.odd_card_center_Xbar
        (hc.sq_eq_one_of_coe_eq_mk ha hA ht) hS hPS hPt hRP hRn hR
    rcases hc.forall_mem_fixA2Plane_or ha hA ht hS' hPS' hP't hR'P' hR'n hR' with h | h
    · left
      rw [← hR'R]
      exact Subgroup.map_mono fun r hr => hc.mem_a2PlaneKernel_iff.mpr (h r hr)
    · right
      rw [← hP'P, ← Subgroup.map_commutator]
      exact Subgroup.map_mono fun c hc' => hc.mem_a2PlaneKernel_iff.mpr (h c hc')
  card_dvd L hLt hLN := hc.card_dvd_of_inf_map_a2PlaneKernel_eq_bot ha' ha hA ht hLt hLN

end CFSG.RankThree.GF2n.Stroth80
