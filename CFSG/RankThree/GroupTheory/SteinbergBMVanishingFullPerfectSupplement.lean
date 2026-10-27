module

public import CFSG.RankThree.GroupTheory.SteinbergBYAschVanishing
public import CFSG.RankThree.GroupTheory.SteinbergBMCentralizerPerfectSupplement
import CFSG.RankThree.GroupTheory.SteinbergCDCentralizedSylowTwo
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem eq_bot_of_normal_of_isSolvable_of_isSimpleGroup {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : ∃ x y : K, x * y ≠ y * x) (T : Subgroup K) [T.Normal] (hT : Group.IsSolvable T) :
    T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hK
    have e : T ≃* K := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
    have hs : Group.IsSolvable K := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hs x y)

theorem le_ker_of_normal_of_isSolvable_of_isSimpleGroup {X K : Type*} [Group X] [Group K]
    [IsSimpleGroup K] (hK : ∃ x y : K, x * y ≠ y * x) (f : X →* K)
    (hf : Function.Surjective f) (T : Subgroup X) [T.Normal] (hT : Group.IsSolvable T) :
    T ≤ f.ker := by
  have : (T.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have : Group.IsSolvable (T.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap T) (f.subgroupMap_surjective T)
  exact (map_eq_bot_iff T).mp (eq_bot_of_normal_of_isSolvable_of_isSimpleGroup hK _ this)

theorem center_eq_bot_of_isSimpleGroup {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : ∃ x y : K, x * y ≠ y * x) : center K = ⊥ :=
  eq_bot_of_normal_of_isSolvable_of_isSimpleGroup hK _
    (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp b.2 a))

theorem isPerfect_of_isSimpleGroup_of_noncomm {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : ∃ x y : K, x * y ≠ y * x) : Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hK
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator K := by
      rw [commutator_eq_closure]
      exact subset_closure (commutator_mem_commutatorSet x y)
    rw [h, mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

theorem exists_projection_of_le_normalizer_of_inf_eq_bot {K N : Subgroup G}
    (hKN : K ≤ normalizer (N : Set G)) (hinf : K ⊓ N = ⊥) :
    ∃ π : (K ⊔ N : Subgroup G) →* K, (∀ x, ((π x : K) : G)⁻¹ * x ∈ N) ∧
      (∀ x, π x = 1 ↔ (x : G) ∈ N) ∧ ∀ k : K, π (inclusion le_sup_left k) = k := by
  have hXN : K ⊔ N ≤ normalizer (N : Set G) := sup_le hKN le_normalizer
  have : (N.subgroupOf (K ⊔ N)).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hXN
  let φ : K.subgroupOf (K ⊔ N) →* (K ⊔ N : Subgroup G) ⧸ N.subgroupOf (K ⊔ N) :=
    (QuotientGroup.mk' _).comp (K.subgroupOf (K ⊔ N)).subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkN : ((k : (K ⊔ N : Subgroup G)) : G) ∈ N :=
      (QuotientGroup.eq_one_iff (N := N.subgroupOf (K ⊔ N)) (k : (K ⊔ N : Subgroup G))).mp hk
    have h1 : ((k : (K ⊔ N : Subgroup G)) : G) ∈ K ⊓ N := ⟨k.2, hkN⟩
    rw [hinf, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (K ⊔ N)) q
    have hx : (x : G) ∈ (K : Set G) * (N : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right K N hKN]
      exact x.2
    obtain ⟨k, hk, n, hn, hkn⟩ := hx
    refine ⟨⟨⟨k, le_sup_left (a := K) hk⟩, hk⟩, ?_⟩
    change QuotientGroup.mk' _ ⟨k, _⟩ = QuotientGroup.mk' _ x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change k⁻¹ * (x : G) ∈ N
    rw [← hkn, inv_mul_cancel_left]
    exact hn
  set e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with he
  refine ⟨(subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ N)).toMonoidHom.comp
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)), fun x => ?_, fun x => ?_, fun k => ?_⟩
  · have h := e.apply_symm_apply (QuotientGroup.mk' (N.subgroupOf (K ⊔ N)) x)
    change QuotientGroup.mk' _ ((e.symm (QuotientGroup.mk' _ x) : K.subgroupOf (K ⊔ N)) :
      (K ⊔ N : Subgroup G)) = _ at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    exact h
  · change subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ N) (e.symm (QuotientGroup.mk' _ x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rfl
  · have hk : e.symm (QuotientGroup.mk' (N.subgroupOf (K ⊔ N)) (inclusion le_sup_left k)) =
        ⟨inclusion le_sup_left k, k.2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    apply Subtype.ext
    change (((e.symm (QuotientGroup.mk' _ (inclusion le_sup_left k)) :
      K.subgroupOf (K ⊔ N)) : (K ⊔ N : Subgroup G)) : G) = k
    rw [hk]
    rfl

theorem isElementaryAbelian_sup_of_le_centralizer {p : ℕ} {B P : Subgroup G}
    (hB : IsElementaryAbelian p B) (hP : IsElementaryAbelian p P)
    (hBP : B ≤ centralizer (P : Set G)) : IsElementaryAbelian p (B ⊔ P : Subgroup G) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hP.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBPc : ∀ x ∈ B, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (hBP hx) y hy).symm
  have hset : ((B ⊔ P : Subgroup G) : Set G) = (B : Set G) * (P : Set G) :=
    coe_mul_of_left_le_normalizer_right B P (hBP.trans (centralizer_le_normalizer _))
  have hmem : ∀ z ∈ B ⊔ P, ∃ x ∈ B, ∃ y ∈ P, x * y = z := fun z hz => by
    have hz' : z ∈ ((B ⊔ P : Subgroup G) : Set G) := hz
    rw [hset] at hz'
    obtain ⟨x, hx, y, hy, rfl⟩ := hz'
    exact ⟨x, hx, y, hy, rfl⟩
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨x₁, hx₁, y₁, hy₁, h₁⟩ := hmem a a.2
    obtain ⟨x₂, hx₂, y₂, hy₂, h₂⟩ := hmem b b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← h₁, ← h₂]
    calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
      _ = x₁ * (x₂ * y₁) * y₂ := by rw [hBPc x₂ hx₂ y₁ hy₁]
      _ = x₁ * x₂ * (y₁ * y₂) := by group
      _ = x₂ * x₁ * (y₂ * y₁) := by rw [hBc x₁ hx₁ x₂ hx₂, hPc y₁ hy₁ y₂ hy₂]
      _ = x₂ * (x₁ * y₂) * y₁ := by group
      _ = x₂ * (y₂ * x₁) * y₁ := by rw [hBPc x₁ hx₁ y₂ hy₂]
      _ = x₂ * y₂ * (x₁ * y₁) := by group
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    obtain ⟨x, hx, y, hy, h⟩ := hmem a a.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← h,
      (show Commute x y from hBPc x hx y hy).mul_pow,
      elemPow_eq_one_of_isElementaryAbelian (A := B) x hx,
      elemPow_eq_one_of_isElementaryAbelian (A := P) y hy, one_mul]

theorem card_sup_of_le_centralizer_of_inf_eq_bot {B P : Subgroup G}
    (hBP : B ≤ centralizer (P : Set G)) (hinf : B ⊓ P = ⊥) :
    Nat.card (B ⊔ P : Subgroup G) = Nat.card B * Nat.card P := by
  set f := B.subtype.noncommCoprod P.subtype
    (fun x y => show Commute (B.subtype x) (P.subtype y) from
      (mem_centralizer_iff.mp (hBP x.2) y y.2).symm) with hf
  have hinj : Function.Injective f := by
    rw [hf, MonoidHom.noncommCoprod_injective, range_subtype, range_subtype, disjoint_iff]
    exact ⟨B.subtype_injective, P.subtype_injective, hinf⟩
  have hrange : f.range = B ⊔ P := by
    rw [hf, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange]

theorem vanishing_centralizing_two_commutator_full_perfect_supplement [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hvan : SteinbergBY.AschVanishing G p) {A B : Subgroup G}
    (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) (hBA : B ≤ A)
    (hBcard : Nat.card B = p ^ 2) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) {K : Subgroup G}
    (hKB : K ≤ centralizer (B : Set G)) (hKs : IsSimpleGroup K)
    (hKn : ∃ x y : K, x * y ≠ y * x) {R : Subgroup G} (hRb : R ≤ centralizer ({b} : Set G))
    (hR2 : IsPGroup 2 R) (hBR : B ≤ normalizer (R : Set G)) (hRB : ⁅R, B⁆ = R)
    (hKR : ⁅K, R⁆ ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G))) :
    let N := inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G))
    let D := inSubgroup perfectResidual (K ⊔ N)
    let V := inSubgroup perfectResidual (D ⊓ centralizer ((R ⊔ B : Subgroup G) : Set G))
    ((K ⊔ N : Subgroup G) : Set G) = (K : Set G) * (N : Set G) ∧ K ⊓ N = ⊥ ∧
      ⁅D, D⁆ = D ∧ ⁅V, V⁆ = V ∧ K ≤ D ∧ V ≤ D ∧
      D ⊓ N = inSubgroup (aschbacherSolvableCore p) D ∧
      (D : Set G) = ((D ⊓ N : Subgroup G) : Set G) * (K : Set G) ∧
      (D : Set G) = ((D ⊓ N : Subgroup G) : Set G) * (V : Set G) ∧
      V ⊓ N = inSubgroup (aschbacherSolvableCore p) V ∧
      Group.IsSolvable (V ⊓ N : Subgroup G) ∧ ¬ p ∣ Nat.card (V ⊓ N : Subgroup G) ∧
      ⁅V, R⁆ = ⊥ ∧ ⁅V, B⁆ = ⊥ ∧ (center V).map V.subtype ≤ V ⊓ N ∧ B ⊓ V = ⊥ ∧
      ∃ ε : V →* K, Function.Surjective ε ∧ (∀ v : V, ((ε v : K) : G)⁻¹ * v ∈ N) ∧
        ε.ker = N.subgroupOf V ∧
        ∀ E : Subgroup G, E ≤ K → IsElementaryAbelian p E → ∀ r : ℕ, Nat.card E = p ^ r →
          ∃ P : Subgroup G, P ≤ V ∧ IsElementaryAbelian p P ∧ Nat.card P = p ^ r ∧
            (P.subgroupOf V).map ε = E.subgroupOf K ∧ P.subgroupOf V ⊓ ε.ker = ⊥ ∧
            B ⊓ P = ⊥ ∧ B ≤ centralizer (P : Set G) ∧ B ⊔ P ≤ normalizer (R : Set G) ∧
            IsElementaryAbelian p (B ⊔ P : Subgroup G) ∧
            Nat.card (B ⊔ P : Subgroup G) = p ^ (r + 2) := by
  intro N D V
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup K := hKs
  have hp2 : p ≠ 2 := by omega
  have hθle : ∀ X : Subgroup G, inSubgroup (aschbacherSolvableCore p) X ≤ X ∧
      ((inSubgroup (aschbacherSolvableCore p) X).subgroupOf X).Normal := fun X => by
    obtain ⟨-, hc, -⟩ := solvable_prime_complement_core_characterization (H := X) hp
    refine ⟨map_subtype_le _, ?_⟩
    have h : (inSubgroup (aschbacherSolvableCore p) X).subgroupOf X =
        aschbacherSolvableCore p X := comap_map_eq_self_of_injective X.subtype_injective _
    rw [h]
    infer_instance
  have hθsol : ∀ X : Subgroup G, Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) X) ∧
      ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) X) := fun X => by
    obtain ⟨hs, -, hpn, -⟩ := solvable_prime_complement_core_characterization (H := X) hp
    refine ⟨Group.isSolvable_of_isSolvable_injective
      (f := ((aschbacherSolvableCore p X).equivMapOfInjective X.subtype
        X.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _), ?_⟩
    rwa [inSubgroup, card_map_of_injective X.subtype_injective]
  have hinfn : ∀ {X Y M : Subgroup G}, X ≤ normalizer (Y : Set G) →
      X ≤ normalizer (M : Set G) → X ≤ normalizer ((Y ⊓ M : Subgroup G) : Set G) :=
    fun hY hM x hx => by
      rw [mem_normalizer_iff]
      intro g
      simp only [mem_inf]
      rw [mem_normalizer_iff.mp (hY hx) g, mem_normalizer_iff.mp (hM hx) g]
  obtain ⟨hNH', hNn'⟩ := hθle (centralizer ({b} : Set G))
  obtain ⟨hNs', hNp'⟩ := hθsol (centralizer ({b} : Set G))
  have hNH : N ≤ centralizer ({b} : Set G) := hNH'
  have hNs : Group.IsSolvable N := hNs'
  have hNp : ¬ p ∣ Nat.card N := hNp'
  have hHN : centralizer ({b} : Set G) ≤ normalizer (N : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hNH).mp hNn'
  have hθmax : ∀ X W : Subgroup G, W ≤ X → X ≤ normalizer (W : Set G) → Group.IsSolvable W →
      ¬ p ∣ Nat.card W → W ≤ inSubgroup (aschbacherSolvableCore p) X := by
    intro X W hWX hXW hWs hWp
    have hmax := (solvable_prime_complement_core_characterization (H := X) hp).2.2.2.1
    have hn : (W.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hWX).mpr hXW
    have hs : Group.IsSolvable (W.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hWX).toMonoidHom) (subgroupOfEquivOfLe hWX).injective
    have hpd : ¬ p ∣ Nat.card (W.subgroupOf X) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hWX).toEquiv]
      exact hWp
    have h := hmax _ hn hs hpd
    intro x hx
    exact ⟨⟨x, hWX hx⟩, h hx, rfl⟩
  have hBe : IsElementaryAbelian p B := isElementaryAbelian_of_le hAe hBA
  have hBp : IsPGroup p B := IsPGroup.of_card hBcard
  have hBH : B ≤ centralizer ({b} : Set G) := fun β hβ => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hBe.is_comm.comm ⟨β, hβ⟩ ⟨b, hbB⟩))
  have hKH : K ≤ centralizer ({b} : Set G) := fun k hk => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (hKB hk) b hbB).symm
  have hKN : K ≤ normalizer (N : Set G) := hKH.trans hHN
  have hBN : B ≤ normalizer (N : Set G) := hBH.trans hHN
  have hRN : R ≤ normalizer (N : Set G) := hRb.trans hHN
  have hKNset : ((K ⊔ N : Subgroup G) : Set G) = (K : Set G) * (N : Set G) :=
    coe_mul_of_left_le_normalizer_right K N hKN
  have hKNbot : K ⊓ N = ⊥ := by
    have : (N.subgroupOf K).Normal :=
      ⟨fun n hn g => (mem_normalizer_iff.mp (hKN g.2) n).mp hn⟩
    have hs : Group.IsSolvable (N.subgroupOf K) := by
      let f : N.subgroupOf K →* N :=
        MonoidHom.mk' (fun x => ⟨((x : K) : G), x.2⟩) fun _ _ => rfl
      exact Group.isSolvable_of_isSolvable_injective (f := f) fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun w : N => (w : G)) h))
    have h := eq_bot_of_normal_of_isSolvable_of_isSimpleGroup hKn _ hs
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxN⟩
    have hx : (⟨x, hxK⟩ : K) ∈ N.subgroupOf K := hxN
    rw [h, mem_bot] at hx
    exact mem_bot.mpr (congrArg Subtype.val hx)
  have hres : ∀ X : Subgroup G, ⁅inSubgroup perfectResidual X, inSubgroup perfectResidual X⁆ =
      inSubgroup perfectResidual X := fun X => by
    have h := Subgroup.isPerfect_iff.mp (perfect_residual_characterization (G := X)).2.2.1
    rw [inSubgroup, ← map_commutator, h]
  have hDperf : ⁅D, D⁆ = D := hres _
  have hKperf : Group.IsPerfect K := isPerfect_of_isSimpleGroup_of_noncomm hKn
  have hKD : K ≤ D := by
    have hperf : Group.IsPerfect (K.subgroupOf (K ⊔ N)) :=
      Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ N)).symm.toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).symm.surjective
    have h := (perfect_residual_transport (MonoidHom.id (K ⊔ N : Subgroup G))).2.2 _ hperf
    exact fun x hx => ⟨⟨x, le_sup_left (a := K) hx⟩, h hx, rfl⟩
  have hDX : D ≤ K ⊔ N := map_subtype_le _
  have hDnormN : D ≤ normalizer (N : Set G) := hDX.trans (sup_le hKN le_normalizer)
  have hDK : (D : Set G) = ((D ⊓ N : Subgroup G) : Set G) * (K : Set G) := by
    apply Set.Subset.antisymm
    · intro d hd
      have hd' : d ∈ D := hd
      have hdX : d⁻¹ ∈ ((K ⊔ N : Subgroup G) : Set G) := hDX (inv_mem hd')
      rw [hKNset] at hdX
      obtain ⟨k, hk, n, hn, hkn'⟩ := hdX
      have hk' : k ∈ K := hk
      have hn' : n ∈ N := hn
      have hkn : k * n = d⁻¹ := hkn'
      have hnk : n⁻¹ = d * k := by
        calc n⁻¹ = (k⁻¹ * (k * n))⁻¹ := by group
          _ = (k⁻¹ * d⁻¹)⁻¹ := by rw [hkn]
          _ = d * k := by group
      have hnD : n⁻¹ ∈ D := by
        rw [hnk]
        exact mul_mem hd' (hKD hk')
      refine ⟨n⁻¹, (mem_inf.mpr ⟨hnD, inv_mem hn'⟩ : n⁻¹ ∈ D ⊓ N), k⁻¹,
        (inv_mem hk' : k⁻¹ ∈ K), ?_⟩
      show n⁻¹ * k⁻¹ = d
      rw [← mul_inv_rev, hkn, inv_inv]
    · rintro _ ⟨n, hn, k, hk, rfl⟩
      have hn' : n ∈ D ⊓ N := hn
      exact (mul_mem (mem_inf.mp hn').1 (hKD hk) : n * k ∈ D)
  obtain ⟨π, hπN, hπker, hπK⟩ := exists_projection_of_le_normalizer_of_inf_eq_bot hKN hKNbot
  set πD : D →* K := π.comp (inclusion hDX) with hπD
  have hπDs : Function.Surjective πD := fun k => ⟨⟨k, hKD k.2⟩, hπK k⟩
  have hDNs : Group.IsSolvable (D ⊓ N : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion inf_le_right) (inclusion_injective _)
  have hDNp : ¬ p ∣ Nat.card (D ⊓ N : Subgroup G) := fun h =>
    hNp (h.trans (card_dvd_of_le inf_le_right))
  have hθD : D ⊓ N = inSubgroup (aschbacherSolvableCore p) D := by
    obtain ⟨hθDD, hθDn⟩ := hθle D
    obtain ⟨hθDs, -⟩ := hθsol D
    apply le_antisymm
    · exact hθmax D (D ⊓ N) inf_le_left (hinfn le_normalizer hDnormN) hDNs hDNp
    · intro x hx
      refine ⟨hθDD hx, ?_⟩
      have hsolv : Group.IsSolvable ((inSubgroup (aschbacherSolvableCore p) D).subgroupOf D) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (subgroupOfEquivOfLe hθDD).toMonoidHom) (subgroupOfEquivOfLe hθDD).injective
      have hle := le_ker_of_normal_of_isSolvable_of_isSimpleGroup hKn πD hπDs _ hsolv
      have hxk : (⟨x, hθDD hx⟩ : D) ∈ πD.ker := hle hx
      exact (hπker _).mp (MonoidHom.mem_ker.mp hxk)
  have hBK : B ≤ centralizer (K : Set G) := le_centralizer_iff.mp hKB
  have hBKN : B ≤ normalizer ((K ⊔ N : Subgroup G) : Set G) := fun β hβ => by
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ (hBK hβ)),
      mem_normalizer_iff_map_conj_eq.mp (hBN hβ)]
  have hRKN : R ≤ normalizer ((K ⊔ N : Subgroup G) : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun r hr x hx => ?_
    have hle : K ⊔ N ≤ (K ⊔ N).comap (MulAut.conj r).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun n hn => ?_)
      · change r * k * r⁻¹ ∈ K ⊔ N
        have hc : ⁅r, k⁆ ∈ N :=
          hKR (by rw [commutator_comm]; exact commutator_mem_commutator hr hk)
        have e : r * k * r⁻¹ = ⁅r, k⁆ * k := by rw [commutatorElement_def]; group
        rw [e]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hk)
      · change r * n * r⁻¹ ∈ K ⊔ N
        exact mem_sup_right ((mem_normalizer_iff.mp (hRN hr) n).mp hn)
    exact hle hx
  have hDchar : normalizer ((K ⊔ N : Subgroup G) : Set G) ≤ normalizer (D : Set G) :=
    le_normalizer_inSubgroup_of_characteristic (F := perfectResidual) (L := K ⊔ N) inferInstance
  have hBD : B ≤ normalizer (D : Set G) := hBKN.trans hDchar
  have hRD : R ≤ normalizer (D : Set G) := hRKN.trans hDchar
  have hDB : ⁅D, B⁆ ≤ inSubgroup (aschbacherSolvableCore p) D := by
    rw [← hθD]
    refine le_inf (le_normalizer_iff_commutator_le_left.mp hBD) ?_
    rw [commutator_le]
    intro d hd β hβ
    have hd' : d ∈ (D : Set G) := hd
    rw [hDK] at hd'
    obtain ⟨n, hn, k, hk, rfl⟩ := hd'
    have hn' : n ∈ N := (mem_inf.mp (show n ∈ D ⊓ N from hn)).2
    have hkβ : k * β = β * k := (mem_centralizer_iff.mp (hKB hk) β hβ).symm
    have e : ⁅n * k, β⁆ = n * (β * n⁻¹ * β⁻¹) := by
      rw [commutatorElement_def]
      calc n * k * β * (n * k)⁻¹ * β⁻¹ = n * (k * β) * k⁻¹ * n⁻¹ * β⁻¹ := by group
        _ = n * (β * k) * k⁻¹ * n⁻¹ * β⁻¹ := by rw [hkβ]
        _ = n * (β * n⁻¹ * β⁻¹) := by group
    rw [e]
    exact mul_mem hn' ((mem_normalizer_iff.mp (hBN hβ) n⁻¹).mp (inv_mem hn'))
  have hRDθ : ⁅R, D⁆ ≤ inSubgroup (aschbacherSolvableCore p) D := by
    rw [← hθD]
    refine le_inf ?_ ?_
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp hRD
    · rw [commutator_le]
      intro r hr d hd
      have hd' : d ∈ (D : Set G) := hd
      rw [hDK] at hd'
      obtain ⟨n, hn, k, hk, rfl⟩ := hd'
      have hn' : n ∈ N := (mem_inf.mp (show n ∈ D ⊓ N from hn)).2
      have e : ⁅r, n * k⁆ = r * n * r⁻¹ * ⁅r, k⁆ * n⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      have hc : ⁅r, k⁆ ∈ N :=
        hKR (by rw [commutator_comm]; exact commutator_mem_commutator hr hk)
      rw [e]
      exact mul_mem (mul_mem ((mem_normalizer_iff.mp (hRN hr) n).mp hn') hc) (inv_mem hn')
  obtain ⟨-, ⟨T₀, hT₀⟩, -⟩ := hvan A hAe hAcard B hBA hBcard b (hBA hbB) hb1
  let _ : MulDistribMulAction B N := MulDistribMulAction.compHom N (inclusion hBN)
  have hsmul : ∀ (β : B) (x : N), ((β • x : N) : G) = (β : G) * x * (β : G)⁻¹ := fun _ _ => rfl
  have hT₀' : ∀ β : B, ∀ x ∈ (T₀ : Subgroup N), β • x = x := by
    intro β x hx
    have hle := commutator_eq_bot_iff_le_centralizer.mp hT₀
    have hxc := hle (mem_map_of_mem N.subtype hx)
    have h : (β : G) * (x : G) = (x : G) * (β : G) :=
      mem_centralizer_iff.mp hxc (β : G) (hBA β.2)
    apply Subtype.ext
    rw [hsmul]
    calc (β : G) * x * (β : G)⁻¹ = x * β * (β : G)⁻¹ := by rw [h]
      _ = x := by group
  have hBcentN : ∀ U : Subgroup G, U ≤ N → IsPGroup 2 U → B ≤ normalizer (U : Set G) →
      U ≤ centralizer (B : Set G) := by
    intro U hUN hU2 hBU
    have hU2' : IsPGroup 2 (U.subgroupOf N) := hU2.comap_subtype
    have hUinv : ∀ β : B, ∀ x ∈ U.subgroupOf N, β • x ∈ U.subgroupOf N := by
      intro β x hx
      rw [mem_subgroupOf] at hx ⊢
      rw [hsmul]
      exact (mem_normalizer_iff.mp (hBU β.2) x).mp hx
    have hmain := CFSG.RankThree.GroupTheory.centralized_sylow_two_controls_invariant_two_subgroups
      (p := p) hBp hNp T₀ hT₀' (U.subgroupOf N) hU2' hUinv
    intro u hu
    rw [mem_centralizer_iff]
    intro β hβ
    have h := hmain ⟨β, hβ⟩ ⟨u, hUN hu⟩ (by rw [mem_subgroupOf]; exact hu)
    have h' := congrArg Subtype.val h
    rw [hsmul] at h'
    calc β * u = β * u * β⁻¹ * β := by group
      _ = u * β := by rw [h']
  have hBcent : ∀ T : Subgroup G, T ≤ inSubgroup (aschbacherSolvableCore p) D →
      IsPGroup 2 T → B ≤ normalizer (T : Set G) → T ≤ centralizer (B : Set G) :=
    fun T hT hT2 hBT => hBcentN T (hT.trans (hθD.symm.le.trans inf_le_right)) hT2 hBT
  obtain ⟨hVperf, hVR, hVB, hDV⟩ :=
    coprime_two_commutator_centralizer_perfect_supplement hp hp2 hBp hDperf hBD hDB hR2 hBR hRB
      hRD hRDθ hBcent
  have hDV' : (D : Set G) = ((D ⊓ N : Subgroup G) : Set G) * (V : Set G) := by
    rw [hθD]
    exact hDV
  have hVD : V ≤ D := (map_subtype_le _).trans inf_le_left
  have hVX : V ≤ K ⊔ N := hVD.trans hDX
  set ε : V →* K := π.comp (inclusion hVX) with hε
  have hεN : ∀ v : V, ((ε v : K) : G)⁻¹ * v ∈ N := fun v => hπN (inclusion hVX v)
  have hεker' : ∀ v : V, ε v = 1 ↔ (v : G) ∈ N := fun v => hπker (inclusion hVX v)
  have hεs : Function.Surjective ε := by
    intro k
    have hk : (k : G) ∈ (D : Set G) := hKD k.2
    rw [hDV'] at hk
    obtain ⟨n, hn, v, hv, hnv'⟩ := hk
    have hnv : n * v = k := hnv'
    have hn' : n ∈ N := (mem_inf.mp (show n ∈ D ⊓ N from hn)).2
    have hvV : v ∈ V := hv
    refine ⟨⟨v, hvV⟩, ?_⟩
    have hv' : inclusion hVX ⟨v, hvV⟩ = (⟨n, mem_sup_right hn'⟩ : (K ⊔ N : Subgroup G))⁻¹ *
        inclusion le_sup_left k := Subtype.ext (by
      change v = n⁻¹ * k
      rw [← hnv, inv_mul_cancel_left])
    change π (inclusion hVX ⟨v, hvV⟩) = k
    rw [hv', map_mul, map_inv, (hπker ⟨n, mem_sup_right hn'⟩).mpr hn', inv_one, one_mul, hπK]
  have hεker : ε.ker = N.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hεker' v
  have hVNs : Group.IsSolvable (V ⊓ N : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion inf_le_right) (inclusion_injective _)
  have hVNp : ¬ p ∣ Nat.card (V ⊓ N : Subgroup G) := fun h =>
    hNp (h.trans (card_dvd_of_le inf_le_right))
  have hθV : V ⊓ N = inSubgroup (aschbacherSolvableCore p) V := by
    obtain ⟨hθVV, hθVn⟩ := hθle V
    obtain ⟨hθVs, -⟩ := hθsol V
    apply le_antisymm
    · exact hθmax V (V ⊓ N) inf_le_left (hinfn le_normalizer (hVD.trans hDnormN)) hVNs hVNp
    · intro x hx
      refine ⟨hθVV hx, ?_⟩
      have hsolv : Group.IsSolvable ((inSubgroup (aschbacherSolvableCore p) V).subgroupOf V) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (subgroupOfEquivOfLe hθVV).toMonoidHom) (subgroupOfEquivOfLe hθVV).injective
      have hle := le_ker_of_normal_of_isSolvable_of_isSimpleGroup hKn ε hεs _ hsolv
      have hxk : (⟨x, hθVV hx⟩ : V) ∈ ε.ker := hle hx
      exact (hεker' _).mp (MonoidHom.mem_ker.mp hxk)
  have hVRc : ⁅V, R⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hVR
  have hVBc : ⁅V, B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hVB
  have hcenK : center K = ⊥ := center_eq_bot_of_isSimpleGroup hKn
  have hZV : (center V).map V.subtype ≤ V ⊓ N := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    have hεz : ε z ∈ center K := by
      rw [mem_center_iff]
      intro k
      obtain ⟨v, rfl⟩ := hεs k
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz v]
    rw [hcenK, mem_bot] at hεz
    exact (hεker' z).mp hεz
  have hBN0 : B ⊓ N = ⊥ := disjoint_iff.mp (disjoint_of_coprime_natCard (by
    rw [hBcard]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hNp)))
  have hBV : B ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxV⟩
    have hxZ : (⟨x, hxV⟩ : V) ∈ center V := mem_center_iff.mpr fun v =>
      Subtype.ext (mem_centralizer_iff.mp (hVB v.2) x hxB).symm
    have hxN : x ∈ N := (hZV ⟨_, hxZ, rfl⟩).2
    have hx : x ∈ B ⊓ N := ⟨hxB, hxN⟩
    rwa [hBN0] at hx
  refine ⟨hKNset, hKNbot, hDperf, hVperf, hKD, hVD, hθD, hDK, hDV', hθV, hVNs, hVNp, hVRc, hVBc,
    hZV, hBV, ε, hεs, hεN, hεker, ?_⟩
  intro E hEK hEe r hEr
  have hEcard' : Nat.card (E.subgroupOf K) = p ^ r := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv, hEr]
  have hcardker : ¬ p ∣ Nat.card ε.ker := by
    rw [hεker, ← card_map_of_injective V.subtype_injective, subgroupOf_map_subtype]
    exact fun h => hNp (h.trans (card_dvd_of_le inf_le_left))
  obtain ⟨P'⟩ : Nonempty (Sylow p ((E.subgroupOf K).comap ε)) := inferInstance
  set P'' : Subgroup V := (P' : Subgroup ((E.subgroupOf K).comap ε)).map
    ((E.subgroupOf K).comap ε).subtype with hP''
  have hP''E : P'' ≤ (E.subgroupOf K).comap ε := map_subtype_le _
  have hP''card : Nat.card P'' = Nat.card P' :=
    card_map_of_injective ((E.subgroupOf K).comap ε).subtype_injective
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp P'.isPGroup'
  have hdisj : P'' ⊓ ε.ker = ⊥ := disjoint_iff.mp (disjoint_of_coprime_natCard (by
    rw [hP''card, hs]
    exact Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcardker)))
  have hker1 : ∀ x ∈ P'', ε x = 1 → x = 1 := fun x hx h1 => by
    have hxk : x ∈ P'' ⊓ ε.ker := ⟨hx, MonoidHom.mem_ker.mpr h1⟩
    rw [hdisj, mem_bot] at hxk
    exact hxk
  have hinj : Function.Injective (ε.domRestrict P'') := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hker1 x x.2 hx)
  have hmapcard : Nat.card (P''.map ε) = Nat.card P'' := by
    rw [← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hmaple : P''.map ε ≤ E.subgroupOf K := map_le_iff_le_comap.mpr hP''E
  have hdvd1 : Nat.card P'' ∣ p ^ r := by
    rw [← hmapcard, ← hEcard']
    exact card_dvd_of_le hmaple
  have hdvd2 : p ^ r ∣ Nat.card P'' := by
    rw [hP''card]
    apply P'.pow_dvd_card_of_pow_dvd_card
    rw [← hEcard']
    exact card_dvd_of_surjective (ε.subgroupComap (E.subgroupOf K))
      (ε.subgroupComap_surjective _ hεs)
  have hP''r : Nat.card P'' = p ^ r := Nat.dvd_antisymm hdvd1 hdvd2
  have hmapeq : P''.map ε = E.subgroupOf K :=
    eq_of_le_of_card_ge hmaple (le_of_eq (by rw [hmapcard, hP''r, hEcard']))
  set P : Subgroup G := P''.map V.subtype with hP
  have hPV : P ≤ V := map_subtype_le _
  have hPsub : P.subgroupOf V = P'' := comap_map_eq_self_of_injective V.subtype_injective P''
  have hPcard : Nat.card P = p ^ r := by
    rw [hP, card_map_of_injective V.subtype_injective, hP''r]
  have hεP : ∀ x ∈ P'', ((ε x : K) : G) ∈ E := fun x hx => hmaple ⟨x, hx, rfl⟩
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPe : IsElementaryAbelian p P := by
    refine { toIsMulCommutative := ⟨⟨fun a c => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyc⟩ := c.2
      have h1 : ε (x * y * (y * x)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        rw [hEc _ (hεP x hx) _ (hεP y hy), mul_inv_cancel]
      have h2 := hker1 _ (mul_mem (mul_mem hx hy) (inv_mem (mul_mem hy hx))) h1
      apply Subtype.ext
      change (a : G) * c = c * a
      rw [← hxa, ← hyc, ← map_mul, ← map_mul, mul_inv_eq_one.mp h2]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨x, hx, hxa⟩ := a.2
      have hεxp : ε (x ^ p) = 1 := by
        rw [map_pow]
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact elemPow_eq_one_of_isElementaryAbelian (A := E) _ (hεP x hx)
      have hxp : x ^ p = 1 := hker1 _ (pow_mem hx p) hεxp
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hxa, ← map_pow, hxp, map_one]
  have hBPbot : B ⊓ P = ⊥ := le_bot_iff.mp ((inf_le_inf_left B hPV).trans hBV.le)
  have hBP : B ≤ centralizer (P : Set G) := fun β hβ => mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_iff.mp (hVB (hPV hx)) β hβ).symm
  have hBPR : B ⊔ P ≤ normalizer (R : Set G) :=
    sup_le hBR ((hPV.trans hVR).trans (centralizer_le_normalizer _))
  refine ⟨P, hPV, hPe, hPcard, ?_, ?_, hBPbot, hBP, hBPR,
    isElementaryAbelian_sup_of_le_centralizer hBe hPe hBP, ?_⟩
  · rw [hPsub]
    exact hmapeq
  · rw [hPsub]
    exact hdisj
  · rw [card_sup_of_le_centralizer_of_inf_eq_bot hBP hBPbot, hBcard, hPcard, ← pow_add, add_comm]

end CFSG.RankThree.GroupTheory.SteinbergBM
