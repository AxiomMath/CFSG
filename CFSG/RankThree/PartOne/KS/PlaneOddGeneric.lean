module

public import CFSG.RankThree.PartOne.S11.PlaneData
public import CFSG.RankThree.PartOne.KS.Lines
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem mem_normalizer_of_map_conj_eq {M : Type*} [Group M] {W : Subgroup M} {a : M}
    (h : W.map (MulAut.conj a).toMonoidHom = W) : a ∈ Subgroup.normalizer (W : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := by
      have h1 : a * y * a⁻¹ = a * x * a⁻¹ := hyx
      simpa using h1
    rw [← this]
    exact hy

theorem conj_aut_apply_eq {T : Type*} [Group T] (e : MulAut T) (u : T) :
    (MulAut.conj (e u) : MulAut T) = e * MulAut.conj u * e⁻¹ := by
  ext y
  simp [MulAut.conj_apply]

section General

variable {M : Type*} [Group M] [Finite M] {p : ℕ} {B A : Subgroup M}

theorem le_normalizer_autPlaneProduct (hp : p.Prime) (hAB : A ≤ B) (hcomm : IsMulCommutative A)
    {t : M} (htA : t ∈ A) : A ≤ Subgroup.normalizer (autPlaneProduct p B A t : Set M) := by
  intro a ha
  have hBmap : B.map (MulAut.conj a).toMonoidHom = B := map_conj_eq_self_of_mem (hAB ha)
  have hAmap : A.map (MulAut.conj a).toMonoidHom = A := map_conj_eq_self_of_mem ha
  have hcomm_t : (MulAut.conj a : MulAut M) t = t := by
    have hc : a * t = t * a := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨t, htA⟩)
    show a * t * a⁻¹ = t
    rw [hc]
    group
  refine mem_normalizer_of_map_conj_eq ?_
  rw [map_autPlaneProduct_mulEquiv hp (MulAut.conj a), hBmap, hAmap, hcomm_t]

theorem le_normalizer_theta_centralizer (hp : p.Prime) (hAB : A ≤ B) (hcomm : IsMulCommutative A)
    {t : M} (htA : t ∈ A) : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore p)
      (B ⊓ centralizer ({t} : Set M))) : Set M) := by
  intro a ha
  have hBmap : B.map (MulAut.conj a).toMonoidHom = B := map_conj_eq_self_of_mem (hAB ha)
  have hcomm_t : (MulAut.conj a : MulAut M) t = t := by
    have hc : a * t = t * a := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨t, htA⟩)
    show a * t * a⁻¹ = t
    rw [hc]
    group
  refine mem_normalizer_of_map_conj_eq ?_
  rw [map_inSubgroup_theta_centralizer_mulEquiv hp (MulAut.conj a), hBmap, hcomm_t]

theorem autPlaneProduct_le_theta (hp : p.Prime) (hAB : A ≤ B) (hcomm : IsMulCommutative A)
    {t : M} (htA : t ∈ A) (ht1 : t ≠ 1) :
    autPlaneProduct p B A t ≤ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ centralizer ({t} : Set M)) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have h1 : a * x⁻¹ * a⁻¹ ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ centralizer ({t} : Set M)) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta_centralizer hp hAB hcomm htA ha) _).mp
        (Subgroup.inv_mem _ hx)
    have := Subgroup.mul_mem _ hx h1
    simpa [mul_assoc] using this
  · exact iInf_le_of_le t (iInf_le_of_le htA (iInf_le _ ht1))

omit [Finite M] in
theorem theta_centralizer_le (p : ℕ) (B : Subgroup M) (t : M) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({t} : Set M)) ≤
      B ⊓ centralizer ({t} : Set M) :=
  Subgroup.map_subtype_le _

theorem not_dvd_card_autPlaneProduct (hp : p.Prime) (hAB : A ≤ B) (hcomm : IsMulCommutative A)
    {t : M} (htA : t ∈ A) (ht1 : t ≠ 1) : ¬ p ∣ Nat.card (autPlaneProduct p B A t) := by
  intro hdvd
  have hdvdθ : Nat.card (autPlaneProduct p B A t) ∣ Nat.card (inSubgroup
      (aschbacherSolvableCore p) (B ⊓ centralizer ({t} : Set M))) :=
    Subgroup.card_dvd_of_le (autPlaneProduct_le_theta hp hAB hcomm htA ht1)
  have hcardθ : Nat.card (inSubgroup (aschbacherSolvableCore p)
      (B ⊓ centralizer ({t} : Set M))) =
      Nat.card (aschbacherSolvableCore p ↥(B ⊓ centralizer ({t} : Set M))) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hnd := (solvable_prime_complement_core_characterization (H := ↥(B ⊓
    centralizer ({t} : Set M))) hp).2.2.1
  exact hnd (hcardθ ▸ hdvd.trans hdvdθ)

theorem not_two_dvd_card_autPlaneProduct_of_centralizer_data {p : ℕ} (hp : p.Prime)
    (hAB : A ≤ B) (hA : IsElementaryAbelian p A) {t : M} (htA : t ∈ A) (ht1 : t ≠ 1)
    (P1 : ∀ v : M, v ^ 2 = 1 → (∀ a ∈ A, a * v = v * a) → v = 1)
    (P2 : ∀ V : Subgroup M, V ≤ Subgroup.centralizer ({t} : Set M) → IsElementaryAbelian 2 V →
      Nat.card V ≡ 1 [MOD p] → V = ⊥) :
    ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) := by
  intro h2W
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative A := hA.toIsMulCommutative
  have hApg : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  set W := autPlaneProduct p B A t with hW
  have hAnormW : A ≤ Subgroup.normalizer (W : Set M) := le_normalizer_autPlaneProduct hp hAB hcomm htA
  have hpW : ¬ p ∣ Nat.card W := not_dvd_card_autPlaneProduct hp hAB hcomm htA ht1
  have hcop : Nat.Coprime p (Nat.card W) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpW
  obtain ⟨S, hSnorm, hSne⟩ :=
    SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial p 2 hp Nat.prime_two
      A W hApg hAnormW hcop h2W
  set P : Subgroup M := (S : Subgroup W).map W.subtype with hP
  have hP2 : IsPGroup 2 P := S.isPGroup'.map W.subtype
  have hPW : P ≤ W := Subgroup.map_subtype_le _
  have hPC : P ≤ Subgroup.centralizer ({t} : Set M) :=
    hPW.trans ((autPlaneProduct_le_theta hp hAB hcomm htA ht1).trans
      ((theta_centralizer_le p B t).trans inf_le_right))
  let V : Subgroup M :=
    { carrier := {x | x ∈ P ∧ x ^ 2 = 1 ∧ ∀ y ∈ P, x * y = y * x}
      mul_mem' := by
        rintro x y ⟨hxP, hx2, hxc⟩ ⟨hyP, hy2, hyc⟩
        refine ⟨P.mul_mem hxP hyP, ?_, fun z hz => ?_⟩
        · have hcxy : Commute x y := hxc y hyP
          rw [hcxy.mul_pow, hx2, hy2, one_mul]
        · rw [mul_assoc, hyc z hz, ← mul_assoc, hxc z hz, mul_assoc]
      one_mem' := ⟨P.one_mem, by simp, fun y _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hxP, hx2, hxc⟩
        refine ⟨P.inv_mem hxP, ?_, fun z hz => ?_⟩
        · rw [inv_pow, hx2, inv_one]
        · exact (Commute.inv_left (hxc z hz : Commute x z)) }
  have hVP : V ≤ P := fun x hx => hx.1
  have hVC : V ≤ Subgroup.centralizer ({t} : Set M) := hVP.trans hPC
  have hPne : P ≠ ⊥ := fun h => hSne h
  have hVne : V ≠ ⊥ := by
    have hPnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
    have hZnt : Nontrivial (Subgroup.center P) := hP2.center_nontrivial
    have hZ2 : IsPGroup 2 (Subgroup.center P) := hP2.to_subgroup _
    have hZcard : 2 ∣ Nat.card (Subgroup.center P) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
      have hk0 : k ≠ 0 := by
        rintro rfl
        have : Nat.card (Subgroup.center P) = 1 := by simpa using hk
        exact absurd (Nat.card_eq_one_iff_unique.mp this).1 (not_subsingleton _)
      rw [hk]
      exact dvd_pow_self 2 hk0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hZcard
    have hxM : ((x : P) : M) ^ 2 = 1 := by
      have : (x : Subgroup.center P) ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
      have := congrArg (fun y : Subgroup.center P => ((y : P) : M)) this
      simpa using this
    have hxV : ((x : P) : M) ∈ V :=
      ⟨(x : P).2, hxM, fun y hy => by
        have h1 := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
        exact (congrArg Subtype.val h1).symm⟩
    intro hV
    have hx1 : ((x : P) : M) = 1 := by
      have := hV ▸ hxV
      simpa using this
    have hx1' : (x : Subgroup.center P) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hx1
    rw [hx1', orderOf_one] at hx
    omega
  have hVea : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (a.2.2.2 b.1 (hVP b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (by simpa using x.2.2.1) }
  have hPinv : ∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hSnorm ha) y).mp hy
  have key : ∀ a ∈ A, ∀ x ∈ V, a * x * a⁻¹ ∈ V := by
    intro a ha x hx
    obtain ⟨hxP, hx2, hxc⟩ := hx
    refine ⟨hPinv a ha x hxP, ?_, fun z hz => ?_⟩
    · rw [conj_pow, hx2]
      group
    · have hz' : a⁻¹ * z * a ∈ P := by
        have := hPinv a⁻¹ (A.inv_mem ha) z hz
        simpa using this
      have h1 := hxc _ hz'
      calc a * x * a⁻¹ * z = a * (x * (a⁻¹ * z * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * z * a) * x) * a⁻¹ := by rw [h1]
        _ = z * (a * x * a⁻¹) := by group
  have hAV : A ≤ Subgroup.normalizer (V : Set M) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key a ha x, fun hx => ?_⟩
    have h2 := key a⁻¹ (A.inv_mem ha) _ hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h2
  have hmod := SignalizerFunctor.Helpers.centralizer_card_modEq p hp A V hApg hAV
  have hfix : V ⊓ Subgroup.centralizer (A : Set M) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxC⟩
    rw [Subgroup.mem_bot]
    exact P1 x hxV.2.1 fun a ha => Subgroup.mem_centralizer_iff.mp hxC a ha
  rw [hfix, Subgroup.card_bot] at hmod
  exact hVne (P2 V hVC hVea hmod)


end General

theorem planeLocalCoreOdd_of_planes_trivial {T : Type} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (h2 : ∀ S : Subgroup (MulAut T), IsPGroup 2 S → S ≤ (MulAut.conj : T →* MulAut T).range)
    (h : ∀ (E : Subgroup (MulAut T)) (U : Subgroup T), PlaneOn p E U → U = ⊥) :
    PlaneLocalCoreOdd p T := by
  intro B hB A hAB hA hAcard t htA ht1 h2W
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative A := hA.toIsMulCommutative
  have hApg : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  set W := autPlaneProduct p B A t with hW
  have hAnormW : A ≤ Subgroup.normalizer (W : Set (MulAut T)) :=
    le_normalizer_autPlaneProduct hp hAB hcomm htA
  have hpW : ¬ p ∣ Nat.card W := not_dvd_card_autPlaneProduct hp hAB hcomm htA ht1
  have hcop : Nat.Coprime p (Nat.card W) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpW
  obtain ⟨S, hSnorm, hSne⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    p 2 hp Nat.prime_two A W hApg hAnormW hcop h2W
  set S' : Subgroup (MulAut T) := (S : Subgroup W).map W.subtype with hS'
  have hS2 : IsPGroup 2 S' := S.isPGroup'.map W.subtype
  have hSinn := h2 S' hS2
  set U : Subgroup T := S'.comap (MulAut.conj : T →* MulAut T) with hU
  have hUpg : IsPGroup 2 U := hS2.comap_of_injective _ hinj
  have hplane : PlaneOn p A U :=
    { prime := hp
      three_lt := hp3
      elementary := hA
      card := hAcard
      two_group := hUpg
      normalized := by
        intro e he u hu
        have hu' : (MulAut.conj u : MulAut T) ∈ S' := hu
        show (MulAut.conj (e u) : MulAut T) ∈ S'
        rw [conj_aut_apply_eq]
        exact (Subgroup.mem_normalizer_iff.mp (hSnorm he) _).mp hu' }
  have hUbot : U = ⊥ := h A U hplane
  obtain ⟨⟨s, hs⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  obtain ⟨u, hu⟩ := hSinn hs
  have huU : u ∈ U := by
    show (MulAut.conj u : MulAut T) ∈ S'
    rw [hu]
    exact hs
  rw [hUbot, Subgroup.mem_bot] at huU
  apply hs1
  rw [← hu, huU, map_one]

theorem planeLocalCoreOdd_of_centralizer_data {T : Type} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (hsurj : Function.Surjective (MulAut.conj : T →* MulAut T))
    (Q1 : ∀ E : Subgroup T, IsElementaryAbelian p E → Nat.card E = p ^ 2 → ∀ v : T, v ^ 2 = 1 →
      (∀ a ∈ E, a * v = v * a) → v = 1)
    (Q2 : ∀ t : T, orderOf t = p → ∀ V : Subgroup T, V ≤ Subgroup.centralizer ({t} : Set T) →
      IsElementaryAbelian 2 V → Nat.card V ≡ 1 [MOD p] → V = ⊥) :
    PlaneLocalCoreOdd p T := by
  intro B hB A hAB hA hAcard t htA ht1
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have : Fact p.Prime := ⟨hp⟩
  let e : T ≃* MulAut T := MulEquiv.ofBijective (MulAut.conj : T →* MulAut T) ⟨hinj, hsurj⟩
  have he : ∀ x, e x = MulAut.conj x := fun x => rfl
  refine not_two_dvd_card_autPlaneProduct_of_centralizer_data hp hAB hA htA ht1 ?_ ?_
  · intro v hv2 hvc
    let E : Subgroup T := A.map e.symm.toMonoidHom
    have hEel : IsElementaryAbelian p E := IsElementaryAbelian.map e.symm.toMonoidHom
    have hEcard : Nat.card E = p ^ 2 := by
      rw [Subgroup.card_map_of_injective e.symm.injective, hAcard]
    have h1 : (e.symm v) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hv2, map_one]
    have h2 := Q1 E hEel hEcard (e.symm v) h1 (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      have := hvc _ hb
      simpa [e.apply_symm_apply] using this)
    have := congrArg e h2
    simpa using this
  · intro V hVC hVea hVmod
    have htord : orderOf t = p := by
      have htp : t ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one htp) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ht1
      · exact h
    let V' : Subgroup T := V.map e.symm.toMonoidHom
    have hV'ea : IsElementaryAbelian 2 V' := IsElementaryAbelian.map e.symm.toMonoidHom
    have hV'card : Nat.card V' = Nat.card V :=
      Subgroup.card_map_of_injective e.symm.injective
    have hV'C : V' ≤ Subgroup.centralizer ({e.symm t} : Set T) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hVC hy)
      apply e.injective
      rw [map_mul, map_mul]
      simpa using h1
    have hord' : orderOf (e.symm t) = p := by rw [MulEquiv.orderOf_eq]; exact htord
    have h3 := Q2 (e.symm t) hord' V' hV'C hV'ea (hV'card ▸ hVmod)
    have h4 : V = ⊥ := by
      have := congrArg (Subgroup.map e.toMonoidHom) h3
      simpa [V', Subgroup.map_map] using this
    exact h4

theorem planeLocalCoreOdd_of_conjugate_witnesses {T : Type} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime)
    (hpinner : ∀ A : Subgroup (MulAut T), IsPGroup p A →
      A ≤ (MulAut.conj : T →* MulAut T).range)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (hDW : ∀ (v : MulAut T) (x : T), orderOf v = 2 → orderOf x = p →
      v * MulAut.conj x = MulAut.conj x * v →
      ∃ l : List T, (∀ g ∈ l, g * x = x * g) ∧
        p ∣ orderOf ((l.map fun g => MulAut.conj g * v * (MulAut.conj g)⁻¹).prod)) :
    PlaneLocalCoreOdd p T := by
  intro B hB A hAB hA hAcard t htA ht1 h2W
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative A := hA.toIsMulCommutative
  have hApg : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  obtain ⟨x, hx⟩ := hpinner A hApg htA
  have htord : orderOf t = p := by
    have htp : t ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one htp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have hxord : orderOf x = p := by
    rw [← orderOf_injective (MulAut.conj : T →* MulAut T) hinj x, hx, htord]
  set W := autPlaneProduct p B A t with hW
  have hWθ := autPlaneProduct_le_theta hp hAB hcomm htA ht1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
  have hu2 : orderOf (u : MulAut T) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have huθ : (u : MulAut T) ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut T))) := hWθ u.2
  have huC : (u : MulAut T) ∈ Subgroup.centralizer ({t} : Set (MulAut T)) :=
    (theta_centralizer_le p B t huθ).2
  have hut : (u : MulAut T) * MulAut.conj x = MulAut.conj x * (u : MulAut T) := by
    rw [hx]; exact Subgroup.mem_centralizer_singleton_iff.mp huC
  obtain ⟨l, hlx, hlord⟩ := hDW u x hu2 hxord hut
  set K : Subgroup (MulAut T) := B ⊓ Subgroup.centralizer ({t} : Set (MulAut T)) with hK
  have hconj : ∀ g ∈ l, MulAut.conj g * (u : MulAut T) * (MulAut.conj g)⁻¹ ∈
      inSubgroup (aschbacherSolvableCore p) K := by
    intro g hg
    have hcB : MulAut.conj g ∈ B := hB ⟨g, rfl⟩
    have hcC : MulAut.conj g ∈ Subgroup.centralizer ({t} : Set (MulAut T)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hx, ← map_mul, ← map_mul, hlx g hg]
    have hcK : MulAut.conj g ∈ K := ⟨hcB, hcC⟩
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp huθ
    have h1 : (⟨MulAut.conj g, hcK⟩ * y * ⟨MulAut.conj g, hcK⟩⁻¹ : K) ∈
        aschbacherSolvableCore p K :=
      (aschbacherSolvableCore_normal p K).conj_mem y hy ⟨MulAut.conj g, hcK⟩
    refine Subgroup.mem_map.mpr ⟨⟨MulAut.conj g, hcK⟩ * y * ⟨MulAut.conj g, hcK⟩⁻¹, h1, ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_subtype] at hyu ⊢
    rw [hyu]
  have hprod : (l.map fun g => MulAut.conj g * (u : MulAut T) * (MulAut.conj g)⁻¹).prod ∈
      inSubgroup (aschbacherSolvableCore p) K := by
    refine Subgroup.list_prod_mem _ fun a ha => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    exact hconj g hg
  have hdvd : orderOf ((l.map fun g => MulAut.conj g * (u : MulAut T) *
      (MulAut.conj g)⁻¹).prod) ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) K) := by
    have := orderOf_dvd_natCard (⟨_, hprod⟩ : inSubgroup (aschbacherSolvableCore p) K)
    rw [← Subgroup.orderOf_coe] at this
    exact this
  have hcard : Nat.card (inSubgroup (aschbacherSolvableCore p) K) =
      Nat.card (aschbacherSolvableCore p ↥K) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hnd := (solvable_prime_complement_core_characterization (H := ↥K) hp).2.2.1
  exact hnd (hcard ▸ (hlord.trans hdvd))

theorem isPGroup_two_le_inner_of_odd_outer {T : Type} [Group T] [Finite T]
    (hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T))) :
    ∀ S : Subgroup (MulAut T), IsPGroup 2 S → S ≤ (MulAut.conj : T →* MulAut T).range := by
  intro S hS a ha
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  obtain ⟨k, hk⟩ := hS ⟨a, ha⟩
  have hak : a ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h1 : orderOf (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
      a) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hak, map_one])
  have h2 : orderOf (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
      a) ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      T)) := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

end CFSG.RankThree.PartOne
