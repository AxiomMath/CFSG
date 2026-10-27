module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.GroupTheory.SteinbergCEFixedResidual
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity

public section

namespace CFSG.RankThree.PartOne.EmbeddingFixedResidual

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_mem_thetaComponents_of_map_eq [Finite G] {p : ℕ} (hp : p.Prime)
    {X₁ X₂ : Subgroup G} {Z₁ : Subgroup X₁} {Z₂ : Subgroup X₂}
    (hZ : Z₁.map X₁.subtype = Z₂.map X₂.subtype) {T₁ : Subgroup Z₁}
    (hT₁ : T₁ ∈ thetaComponents p Z₁) :
    ∃ T₂ ∈ thetaComponents p Z₂,
      (T₂.map Z₂.subtype).map X₂.subtype = (T₁.map Z₁.subtype).map X₁.subtype := by
  let e₁ := Z₁.equivMapOfInjective X₁.subtype X₁.subtype_injective
  let e₂ := Z₂.equivMapOfInjective X₂.subtype X₂.subtype_injective
  let e : Z₁ ≃* Z₂ := e₁.trans ((MulEquiv.subgroupCongr hZ).trans e₂.symm)
  have he : ∀ z : Z₁, (((e z : Z₂) : X₂) : G) = ((z : X₁) : G) := fun z => by
    have h := congrArg (fun w : Z₂.map X₂.subtype => (w : G))
      (e₂.apply_symm_apply (MulEquiv.subgroupCongr hZ (e₁ z)))
    exact h
  refine ⟨T₁.map e.toMonoidHom, map_mulEquiv_mem_thetaComponents hp e hT₁, ?_⟩
  simp only [Subgroup.map_map]
  exact congrArg (Subgroup.map · T₁) (MonoidHom.ext he)

theorem eq_of_perfect_le_of_mem_thetaComponentsAt [Finite G] {p : ℕ} (hp : p.Prime) {a : G}
    {X J V : Subgroup G} (hX : X ∈ thetaComponentsAt p a) (hJ : J ∈ thetaComponentsAt p a)
    (hV : V ≠ ⊥) (hVp : Group.IsPerfect V) (hVX : V ≤ X) (hVJ : V ≤ J) : X = J := by
  set C := Subgroup.centralizer ({a} : Set G)
  obtain ⟨hXC, hX'⟩ := mem_thetaComponentsAt_iff.mp hX
  obtain ⟨hJC, hJ'⟩ := mem_thetaComponentsAt_iff.mp hJ
  have hVC : V ≤ C := hVX.trans hXC
  have hV' : V.subgroupOf C ≠ ⊥ := fun h => hV (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVC, h, Subgroup.map_bot])
  have hVp' : Group.IsPerfect (V.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hVC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hVC).symm.surjective
  have heq := theta_component_eq_of_perfect_le hp hX' hJ' hV' hVp'
    (Subgroup.subgroupOf_mono C hVX) (Subgroup.subgroupOf_mono C hVJ)
  rw [← Subgroup.map_subgroupOf_eq_of_le hXC, ← Subgroup.map_subgroupOf_eq_of_le hJC, heq]

theorem centralizer_ne_top_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {a : G} (ha : a ≠ 1) : Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  have hz : a ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
    have : g ∈ Subgroup.centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact ha (Subgroup.mem_bot.mp (h ▸ hz))
  · obtain ⟨x, y, hxy⟩ := hnonab
    exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm

theorem orderOf_eq_of_isElementaryAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    [IsElementaryAbelian p A] {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) : orderOf a = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haA) ha1

theorem commute_mem_centralizer {a c : G} (h : c * a = a * c) :
    c ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr h

variable {p : ℕ}

theorem forall_mem_zpowers_trivial_action {L : Subgroup G} {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G))
    (htriv : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L) :
    ∀ d ∈ Subgroup.zpowers a, d ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L :=
  fun _ hd => (mem_thetaQuotientCentralizer_iff.mp (Subgroup.zpowers_le.mpr
    (mem_thetaQuotientCentralizer_iff.mpr ⟨Subgroup.mem_top a, haL, htriv⟩) hd)).2

theorem trivial_action_of_commutator_le {L : Subgroup G} {a : G}
    (h : ⁅L, Subgroup.zpowers a⁆ ≤ inSubgroup (aschbacherSolvableCore p) L) :
    ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L := fun l hl => by
  have hmem := h (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers a))
  have heq : a * l * a⁻¹ * l⁻¹ = (⁅l, a⁆)⁻¹ := by
    rw [commutatorElement_inv, commutatorElement_def]
  rw [heq]
  exact Subgroup.inv_mem _ hmem

theorem trivial_action_of_eq_sup_centralizing {K J : Subgroup G} {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haJ : J ≤ Subgroup.centralizer ({a} : Set G))
    (hKJ : K = (K ⊓ J) ⊔ inSubgroup (aschbacherSolvableCore p) K) :
    ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K := by
  intro k hk
  obtain ⟨m, hm, n, hn, rfl⟩ := exists_mul_of_eq_sup_core inf_le_left hKJ hk
  have hcomm : m * a = a * m := Subgroup.mem_centralizer_singleton_iff.mp (haJ hm.2)
  have h1 : a * n * a⁻¹ * n⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K :=
    Subgroup.mul_mem _ (conj_mem_inSubgroup_aschbacherSolvableCore haK hn)
      (Subgroup.inv_mem _ hn)
  have h2 := conj_mem_inSubgroup_aschbacherSolvableCore (Subgroup.le_normalizer hm.1) h1
  have heq : a * (m * n) * a⁻¹ * (m * n)⁻¹ = m * (a * n * a⁻¹ * n⁻¹) * m⁻¹ := by
    calc a * (m * n) * a⁻¹ * (m * n)⁻¹ = (a * m) * n * a⁻¹ * n⁻¹ * m⁻¹ := by group
      _ = (m * a) * n * a⁻¹ * n⁻¹ * m⁻¹ := by rw [← hcomm]
      _ = m * (a * n * a⁻¹ * n⁻¹) * m⁻¹ := by group
  rw [heq]
  exact h2

theorem surjective_inclusion_quotient {L M : Subgroup G} (hML : M ≤ L)
    (hLM : L = M ⊔ inSubgroup (aschbacherSolvableCore p) L) :
    Function.Surjective
      ((QuotientGroup.mk' (aschbacherSolvableCore p L)).comp (Subgroup.inclusion hML)) := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨m, hm, n, hn, hmn⟩ := exists_mul_of_eq_sup_core hML hLM l.2
  have hnL : n ∈ L := Subgroup.map_subtype_le _ hn
  refine ⟨⟨m, hm⟩, ?_⟩
  change QuotientGroup.mk' (aschbacherSolvableCore p L) (Subgroup.inclusion hML ⟨m, hm⟩) =
    QuotientGroup.mk' (aschbacherSolvableCore p L) l
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  obtain ⟨n', hn', hn'eq⟩ := id hn
  have hn'n : n' = ⟨n, hnL⟩ := Subtype.ext hn'eq
  have : (Subgroup.inclusion hML ⟨m, hm⟩)⁻¹ * l = ⟨n, hnL⟩ := Subtype.ext (by
    change m⁻¹ * (l : G) = n
    rw [← hmn, inv_mul_cancel_left])
  rw [this, ← hn'n]
  exact hn'

theorem fixed_residual_ambient [Finite G] (hp : p.Prime) {c a : G} (hac : c * a = a * c)
    (hord : ∃ k : ℕ, orderOf a = p ^ k) {W : Subgroup G} (hW : W ∈ thetaComponentsAt p c)
    (haW : a ∈ Subgroup.normalizer (W : Set G))
    (htriv : ∀ w ∈ W, a * w * a⁻¹ * w⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) W) :
    inSubgroup (aschbacherSolvableCore p) W ⊔
        inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({a} : Set G)) = W ∧
      ∃ P' ∈ thetaComponentsAt p (⟨c, commute_mem_centralizer hac⟩ :
          Subgroup.centralizer ({a} : Set G)),
        P'.map (Subgroup.centralizer ({a} : Set G)).subtype =
          inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨hWH, hW₀⟩ := mem_thetaComponentsAt_iff.mp hW
  set H₀ := Subgroup.centralizer ({c} : Set G) with hH₀
  set W₀ := W.subgroupOf H₀ with hW₀def
  have haH₀ : a ∈ H₀ := Subgroup.mem_centralizer_singleton_iff.mpr hac.symm
  set a₀ : H₀ := ⟨a, haH₀⟩ with ha₀
  have hD₀p : IsPGroup p (Subgroup.zpowers a₀) := by
    obtain ⟨k, hk⟩ := hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe a₀]; exact hk)
  have ha₀W : a₀ ∈ Subgroup.normalizer (W₀ : Set H₀) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := Subgroup.mem_normalizer_iff.mp haW (x : G)
    rw [hW₀def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h
  have hDW : Subgroup.zpowers a₀ ≤ Subgroup.normalizer (W₀ : Set H₀) :=
    Subgroup.zpowers_le.mpr ha₀W
  have hW₀map : W₀.map H₀.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWH
  have hθW : (inSubgroup (aschbacherSolvableCore p) W₀).map H₀.subtype =
      inSubgroup (aschbacherSolvableCore p) W := by
    rw [Sec9A.map_inSubgroup_theta_of_injective hp H₀.subtype H₀.subtype_injective, hW₀map]
  have hmemθ : ∀ x : H₀, (x : G) ∈ inSubgroup (aschbacherSolvableCore p) W →
      x ∈ inSubgroup (aschbacherSolvableCore p) W₀ := fun x hx => by
    rw [← hθW] at hx
    exact (Subgroup.mem_map_iff_mem H₀.subtype_injective).mp hx
  have hker : ∀ d : Subgroup.zpowers a₀, d ∈ (thetaQuotientAction p hDW).ker := by
    have h1 : (⟨a₀, Subgroup.mem_zpowers a₀⟩ : Subgroup.zpowers a₀) ∈
        (thetaQuotientAction p hDW).ker := by
      rw [mem_ker_thetaQuotientAction_iff]
      intro k hk
      exact hmemθ _ (htriv k hk)
    intro d
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp d.2
    have hd : d = (⟨a₀, Subgroup.mem_zpowers a₀⟩ : Subgroup.zpowers a₀) ^ n :=
      Subtype.ext hn.symm
    rw [hd]
    exact zpow_mem h1 n
  have htriv₀ : thetaQuotientAction p hDW = 1 :=
    MonoidHom.ext fun d => (MonoidHom.mem_ker.mp (hker d))
  obtain ⟨hsup, hle, hmem⟩ := theta_component_trivial_quotient_action_fixed_residual_subnormal hp
    hW₀.2.1 hW₀.2.2 hD₀p hDW htriv₀
  have hCD : (Subgroup.centralizer (Subgroup.zpowers a₀ : Set H₀)).map H₀.subtype =
      H₀ ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [← centralizer_singleton_eq_centralizer_zpowers]
    exact map_subtype_centralizer_singleton H₀ a₀
  have hW₀CD : (W₀ ⊓ Subgroup.centralizer (Subgroup.zpowers a₀ : Set H₀)).map H₀.subtype =
      W ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.map_inf_eq _ _ H₀.subtype H₀.subtype_injective, hW₀map, hCD, ← inf_assoc,
      inf_eq_left.mpr hWH]
  have hP₀ : (inSubgroup perfectResidual
      (W₀ ⊓ Subgroup.centralizer (Subgroup.zpowers a₀ : Set H₀))).map H₀.subtype =
      inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [map_inSubgroup_perfectResidual_of_injective H₀.subtype H₀.subtype_injective, hW₀CD]
  refine ⟨?_, ?_⟩
  · have h := congrArg (Subgroup.map H₀.subtype) hsup
    rwa [Subgroup.map_sup, hθW, hP₀, hW₀map] at h
  · set c' : Subgroup.centralizer ({a} : Set G) := ⟨c, commute_mem_centralizer hac⟩ with hc'
    have hZ : (Subgroup.centralizer (Subgroup.zpowers a₀ : Set H₀)).map H₀.subtype =
        (Subgroup.centralizer ({c'} : Set (Subgroup.centralizer ({a} : Set G)))).map
          (Subgroup.centralizer ({a} : Set G)).subtype := by
      rw [hCD, map_subtype_centralizer_singleton, inf_comm]
    obtain ⟨T₂, hT₂, hT₂eq⟩ := exists_mem_thetaComponents_of_map_eq hp hZ hmem
    refine ⟨_, ⟨T₂, hT₂, rfl⟩, ?_⟩
    rw [hT₂eq, Subgroup.map_subgroupOf_eq_of_le hle, hP₀]

theorem fixedPointSubgroup_map_surjective {X D Q : Type*} [Group X] [Finite X] [Group D]
    [Finite D] [Group Q] [MulDistribMulAction D X] (hp : p.Prime) (hD : IsPGroup p D) (ψ : X →* Q)
    (hψ : Function.Surjective ψ) (hks : Group.IsSolvable ψ.ker) (hkp : ¬ p ∣ Nat.card ψ.ker)
    (hinv : ∀ (d : D) (x : X), ψ (d • x) = ψ x) :
    Function.Surjective (ψ.comp (fixedPointSubgroup D X).subtype) := by
  have : Fact p.Prime := ⟨hp⟩
  set N := ψ.ker with hN
  have hNinv : CFSG.IsInvariant D X N := ⟨fun d g => by
    simp only [hN, MonoidHom.mem_ker, hinv d g]⟩
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hkp)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting N hNinv hks hcop
  have hCtop : (fixedPointSubgroup D X).map (QuotientGroup.mk' N) = ⊤ := by
    let : MulDistribMulAction D (X ⧸ N) :=
      CFSG.quotientMulDistribMulAction (A := D) (G := X) N hNinv
    let : MulAction.QuotientAction D N := CFSG.quotientAction_of_isInvariant (A := D) N hNinv
    rw [← hlift, eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    intro d
    rw [MulAction.Quotient.smul_coe (H := N) d x]
    exact QuotientGroup.eq.mpr (by
      simp only [hN, MonoidHom.mem_ker, map_mul, map_inv, hinv d x, inv_mul_cancel])
  intro q
  obtain ⟨x, rfl⟩ := hψ q
  have hx : QuotientGroup.mk' N x ∈ (fixedPointSubgroup D X).map (QuotientGroup.mk' N) :=
    hCtop ▸ Subgroup.mem_top _
  obtain ⟨c, hc, hcx⟩ := hx
  refine ⟨⟨c, hc⟩, ?_⟩
  have h : c⁻¹ * x ∈ N := QuotientGroup.eq.mp hcx
  rw [hN, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem not_isSolvable_inf_centralizer [Finite G] (hp : p.Prime) {L M : Subgroup G} {a : G}
    (hML : M ≤ L) (hLM : L = M ⊔ inSubgroup (aschbacherSolvableCore p) L)
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (haM : a ∈ Subgroup.normalizer (M : Set G))
    (hord : ∃ k : ℕ, orderOf a = p ^ k) (hq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (htriv : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L) :
    ¬ Group.IsSolvable ↥(M ⊓ Subgroup.centralizer ({a} : Set G)) := by
  intro hsol
  have hDM : Subgroup.zpowers a ≤ Subgroup.normalizer (M : Set G) := Subgroup.zpowers_le.mpr haM
  let _ : MulDistribMulAction (Subgroup.zpowers a) M := conjActionOn hDM
  have hsmul : ∀ (d : Subgroup.zpowers a) (m : M), ((d • m : M) : G) = (d : G) * m * (d : G)⁻¹ :=
    fun _ _ => rfl
  have hDp : IsPGroup p (Subgroup.zpowers a) := by
    obtain ⟨k, hk⟩ := hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  let ψ : M →* L ⧸ aschbacherSolvableCore p L :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hML)
  have hψ : Function.Surjective ψ := surjective_inclusion_quotient hML hLM
  obtain ⟨hθs, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  let ι : ψ.ker →* aschbacherSolvableCore p L :=
    ((Subgroup.inclusion hML).comp ψ.ker.subtype).codRestrict _
      fun y => (QuotientGroup.eq_one_iff _).mp y.2
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : aschbacherSolvableCore p L => ((z : L) : G)) h))
  have hks : Group.IsSolvable ψ.ker := Group.isSolvable_of_isSolvable_injective hι
  have hkp : ¬ p ∣ Nat.card ψ.ker := fun h => hθp (h.trans (Subgroup.card_dvd_of_injective ι hι))
  have hinv : ∀ (d : Subgroup.zpowers a) (m : M), ψ (d • m) = ψ m := fun d m => by
    obtain ⟨-, hdtriv⟩ := forall_mem_zpowers_trivial_action haL htriv (d : G) d.2
    have h := hdtriv ((m : G)⁻¹) (L.inv_mem (hML m.2))
    change QuotientGroup.mk' _ (Subgroup.inclusion hML (d • m)) =
      QuotientGroup.mk' _ (Subgroup.inclusion hML m)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine (Subgroup.mem_map_iff_mem L.subtype_injective).mp ?_
    have heq : ((d • m : M) : G)⁻¹ * (m : G) = (d : G) * (m : G)⁻¹ * (d : G)⁻¹ * ((m : G)⁻¹)⁻¹ := by
      rw [hsmul]
      group
    have h2 : ((d • m : M) : G)⁻¹ * (m : G) ∈ inSubgroup (aschbacherSolvableCore p) L := by
      rw [heq]
      exact h
    exact h2
  have hsurj := fixedPointSubgroup_map_surjective hp hDp ψ hψ hks hkp hinv
  let j : fixedPointSubgroup (Subgroup.zpowers a) M →* ↥(M ⊓ Subgroup.centralizer ({a} : Set G)) :=
    MonoidHom.codRestrict ((M.subtype).comp (fixedPointSubgroup (Subgroup.zpowers a) M).subtype)
      _ fun c => ⟨c.1.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
        have h := congrArg Subtype.val (c.2 ⟨a, Subgroup.mem_zpowers a⟩)
        rw [hsmul] at h
        have h' : a * (c.1 : G) = (c.1 : G) * a := by
          calc a * (c.1 : G) = a * c.1 * a⁻¹ * a := by group
            _ = (c.1 : G) * a := by rw [show a * (c.1 : G) * a⁻¹ = c.1 from h]
        exact h'.symm)⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(M ⊓ Subgroup.centralizer ({a} : Set G)) => (z : G)) h))
  have hsolC : Group.IsSolvable (fixedPointSubgroup (Subgroup.zpowers a) M) :=
    Group.isSolvable_of_isSolvable_injective hj
  have hsolQ : Group.IsSolvable (L ⧸ aschbacherSolvableCore p L) :=
    Group.isSolvable_of_surjective hsurj
  have := LocalCores.isQuasisimple_nontrivial hq
  have := hq.1
  exact Group.IsPerfect.not_isSolvable _ hsolQ

theorem isPerfect_inSubgroup_perfectResidual [Finite G] (X : Subgroup G) :
    Group.IsPerfect (inSubgroup perfectResidual X) := by
  have := (perfect_residual_characterization (G := X)).2.2.1
  exact Group.IsPerfect.map X.subtype

theorem ne_bot_inSubgroup_perfectResidual_of_not_isSolvable [Finite G] {X : Subgroup G}
    (h : ¬ Group.IsSolvable X) : inSubgroup perfectResidual X ≠ ⊥ := fun hbot =>
  h ((perfect_residual_characterization (G := X)).2.2.2.2.2.mp
    ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hbot))

end CFSG.RankThree.PartOne.EmbeddingFixedResidual
