module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step198DProof

section SLTwo

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_isPGLAt (D : SLTwoData X π p f K) (x : X) : ∃ y, Sec4.IsPGLAt D.e x y := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact D.piField.unitary
  obtain ⟨l, hl, i, -, j, -, rfl⟩ := D.exists_normal_form x
  exact ⟨_, Sec4.isPGLAt_mul D.e (Sec4.isPGLAt_mul D.e (Sec4.isPGLAt_of_mem D.e hπ hl)
    (Sec4.isPGLAt_of_mem_centralizer D.e (Subgroup.pow_mem _ D.mem_centralizer i)))
    (Sec4.isPGLAt_pow D.isPGLAt_a j)⟩

theorem card_centralizer_le [Finite X] (D : SLTwoData X π p f K) :
    Nat.card (Subgroup.centralizer (D.L₀ : Set X)) ≤ 9 := by
  set Z := D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X) with hZ
  let F : Z × Fin 3 → Subgroup.centralizer (D.L₀ : Set X) := fun zi =>
    ⟨(zi.1 : X) * D.u ^ (zi.2 : ℕ),
      Subgroup.mul_mem _ zi.1.2.2 (Subgroup.pow_mem _ D.mem_centralizer _)⟩
  have hF : Function.Surjective F := by
    rintro ⟨z, hz⟩
    obtain ⟨l, hl, i, hi, rfl⟩ := D.exists_of_mem_centralizer hz
    exact ⟨(⟨l, hl⟩, ⟨i, hi⟩), rfl⟩
  calc Nat.card (Subgroup.centralizer (D.L₀ : Set X)) ≤ Nat.card (Z × Fin 3) :=
        Nat.card_le_card_of_surjective F hF
    _ = Nat.card Z * 3 := by rw [Nat.card_prod, Nat.card_fin]
    _ ≤ 3 * 3 := Nat.mul_le_mul_right 3 D.card_inf_centralizer_le

theorem nine_le_card_inf [Finite X] (D : SLTwoData X π p f K) {A E : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hAE : A ≤ Subgroup.normalizer (E : Set X)) (hEA : E ≤ Subgroup.normalizer (A : Set X))
    (hEC : 9 ≤ Nat.card (E ⊓ Subgroup.centralizer (D.L₀ : Set X) : Subgroup X))
    {c : X} (hcA : c ∈ A) (hcC : c ∈ Subgroup.centralizer (D.L₀ : Set X)) (hc1 : c ≠ 1) :
    9 ≤ Nat.card (A ⊓ E : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (D.L₀ : Set X) with hC
  have hCcard : Nat.card C ≤ 9 := card_centralizer_le D
  have hCE : C ≤ E := by
    have heq : E ⊓ C = C := Subgroup.eq_of_le_of_card_ge inf_le_right (hCcard.trans hEC)
    rw [← heq]
    exact inf_le_left
  have hcE : c ∈ E := hCE hcC
  have hco : orderOf c = 3 := orderOf_eq_prime (hA.2 c hcA) hc1
  have hcAE : Subgroup.zpowers c ≤ A ⊓ E := Subgroup.zpowers_le.mpr ⟨hcA, hcE⟩
  have hge3 : 3 ≤ Nat.card (A ⊓ E : Subgroup X) := by
    have := Subgroup.card_le_of_le hcAE
    rwa [Nat.card_zpowers, hco] at this
  have hdvd : Nat.card (A ⊓ E : Subgroup X) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_contra hlt
  have hk1 : k = 1 := by
    interval_cases k <;> simp_all
  subst hk1
  rw [pow_one] at hk
  have hAEc : A ⊓ E = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge hcAE (by rw [hk, Nat.card_zpowers, hco])).symm
  have hcomm : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ C := by
    intro a ha e he
    have h1 : a * e * a⁻¹ * e⁻¹ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (hEA he) a⁻¹).mp (A.inv_mem ha)
      simpa [mul_assoc] using A.mul_mem ha this
    have h2 : a * e * a⁻¹ * e⁻¹ ∈ E :=
      E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAE ha) e).mp he) (E.inv_mem he)
    have h3 : a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c := hAEc ▸ ⟨h1, h2⟩
    exact Subgroup.zpowers_le.mpr hcC h3
  set P := A ⊔ E with hP
  have h1 : Nat.card P * Nat.card (A ⊓ E : Subgroup X) = Nat.card A * Nat.card E :=
    CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf hAE
  rw [hk, hA27, hE27] at h1
  have hPcard : Nat.card P = 243 := by omega
  have hlift : ∀ x ∈ P, ∃ y, Sec4.IsPGLAt D.e x y := fun x _ => exists_isPGLAt D x
  set ψ := Sec4.pglHom D.piField D.modThree P hlift with hψ
  have hcard : Nat.card P = Nat.card (P ⊓ C : Subgroup X) * Nat.card ψ.range :=
    Sec4.card_eq_card_inf_mul_card_range
  have hker : Nat.card (P ⊓ C : Subgroup X) ≤ 9 :=
    (Subgroup.card_le_of_le inf_le_right).trans hCcard
  have hψ1 : ∀ x : P, (x : X) ∈ C → ψ x = 1 := fun x hx =>
    (Sec4.pglHom_eq_one_iff (hK := D.piField) (hq := D.modThree) (hA' := hlift) x).mpr hx
  have hAP : A ≤ P := le_sup_left
  have hEP : E ≤ P := le_sup_right
  have hdec : ∀ x ∈ P, ∃ a ∈ A, ∃ e ∈ E, a * e = x := by
    intro x hx
    have hx' : x ∈ ((A ⊔ E : Subgroup X) : Set X) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A E hAE] at hx'
    obtain ⟨a, ha, e, he, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, e, he, rfl⟩
  have cAA : ∀ a (ha : a ∈ A) a' (ha' : a' ∈ A),
      Commute (ψ ⟨a, hAP ha⟩) (ψ ⟨a', hAP ha'⟩) := by
    intro a ha a' ha'
    have h2 : (⟨a, hAP ha⟩ : P) * ⟨a', hAP ha'⟩ = ⟨a', hAP ha'⟩ * ⟨a, hAP ha⟩ :=
      Subtype.ext (show a * a' = a' * a from
        congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨a', ha'⟩))
    change ψ _ * ψ _ = ψ _ * ψ _
    rw [← map_mul, ← map_mul, h2]
  have cEE : ∀ e (he : e ∈ E) e' (he' : e' ∈ E),
      Commute (ψ ⟨e, hEP he⟩) (ψ ⟨e', hEP he'⟩) := by
    intro e he e' he'
    have h2 : (⟨e, hEP he⟩ : P) * ⟨e', hEP he'⟩ = ⟨e', hEP he'⟩ * ⟨e, hEP he⟩ :=
      Subtype.ext (show e * e' = e' * e from
        congrArg Subtype.val (hE.1.is_comm.comm (⟨e, he⟩ : E) ⟨e', he'⟩))
    change ψ _ * ψ _ = ψ _ * ψ _
    rw [← map_mul, ← map_mul, h2]
  have cAE : ∀ a (ha : a ∈ A) e (he : e ∈ E),
      Commute (ψ ⟨a, hAP ha⟩) (ψ ⟨e, hEP he⟩) := by
    intro a ha e he
    have h2 : ψ (⟨a, hAP ha⟩ * ⟨e, hEP he⟩ * (⟨a, hAP ha⟩ : P)⁻¹ * (⟨e, hEP he⟩ : P)⁻¹) = 1 :=
      hψ1 _ (hcomm a ha e he)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    change ψ _ * ψ _ = ψ _ * ψ _
    calc ψ ⟨a, hAP ha⟩ * ψ ⟨e, hEP he⟩ = (ψ ⟨a, hAP ha⟩ * ψ ⟨e, hEP he⟩ *
        (ψ ⟨a, hAP ha⟩)⁻¹ * (ψ ⟨e, hEP he⟩)⁻¹) * (ψ ⟨e, hEP he⟩ * ψ ⟨a, hAP ha⟩) := by group
      _ = ψ ⟨e, hEP he⟩ * ψ ⟨a, hAP ha⟩ := by rw [h2, one_mul]
  have hrcomm : ∀ z ∈ ψ.range, ∀ w ∈ ψ.range, z * w = w * z := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain ⟨a, ha, e, he, hx⟩ := hdec x x.2
    obtain ⟨a', ha', e', he', hy⟩ := hdec y y.2
    have hxe : x = ⟨a, hAP ha⟩ * ⟨e, hEP he⟩ := Subtype.ext hx.symm
    have hye : y = ⟨a', hAP ha'⟩ * ⟨e', hEP he'⟩ := Subtype.ext hy.symm
    rw [hxe, hye, map_mul, map_mul]
    exact (((cAA a ha a' ha').mul_right (cAE a ha e' he')).mul_left
      ((cAE a' ha' e he).symm.mul_right (cEE e he e' he'))).eq
  have hrexp : ∀ z ∈ ψ.range, z ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, ha, e, he, hx⟩ := hdec x x.2
    have hxe : x = ⟨a, hAP ha⟩ * ⟨e, hEP he⟩ := Subtype.ext hx.symm
    have ha3 : (⟨a, hAP ha⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a ha)
    have he3 : (⟨e, hEP he⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hE.2 e he)
    rw [hxe, map_mul, (cAE a ha e he).mul_pow, ← map_pow, ← map_pow, ha3, he3, map_one,
      one_mul]
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau D.piField D.modThree
  have hrange : Nat.card ψ.range ≤ 9 :=
    Sec4.card_le_nine_of_comm (D.piField.three_ne_zero D.modThree) hτ hτ1 ψ.range hrcomm hrexp
  have := Nat.mul_le_mul hker hrange
  omega

end SLTwo

section Transfer

theorem card_map_of_injOn {T Y : Type*} [Group T] [Group Y] (φ : T →* Y) {S : Subgroup T}
    (h : Set.InjOn φ (S : Set T)) : Nat.card (S.map φ) = Nat.card S := by
  change Nat.card ((S.map φ : Subgroup Y) : Set Y) = Nat.card (S : Set T)
  rw [Subgroup.coe_map, Nat.card_image_of_injOn h]

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {S : Subgroup G}
    (hS : CFSG.Assembly.IsElemAbelian p S) (K : Subgroup G) :
    CFSG.Assembly.IsElemAbelian p (S.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hS K

theorem subgroupOf_le_normalizer {G : Type*} [Group G] {S S' : Subgroup G}
    (h : S ≤ Subgroup.normalizer (S' : Set G)) (K : Subgroup G) :
    S.subgroupOf K ≤ Subgroup.normalizer ((S'.subgroupOf K : Subgroup K) : Set K) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_subgroupOf.mp ha)) x

theorem map_le_normalizer_map {T Y : Type*} [Group T] [Group Y] [Finite Y] (φ : T →* Y)
    {S S' : Subgroup T} (h : S ≤ Subgroup.normalizer (S' : Set T)) :
    S.map φ ≤ Subgroup.normalizer ((S'.map φ : Subgroup Y) : Set Y) := by
  rintro _ ⟨s, hs, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨s', hs', rfl⟩ := hy
  exact ⟨s * s' * s⁻¹, (Subgroup.mem_normalizer_iff.mp (h hs) s').mp hs', by simp⟩

theorem nine_le_card_of_not_isCyclic {T : Type*} [Group T] [Finite T] {S : Subgroup T}
    (hexp : ∀ x ∈ S, x ^ 3 = 1) (hS : ¬ IsCyclic S) : 9 ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  by_contra hlt
  have hn1 : n ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact hS isCyclic_of_subsingleton
  · exact hS (isCyclic_of_prime_card (p := 3) (by simpa using hn))

end Transfer

end Step198DProof

open Step198DProof

theorem step198D_of (h197 : Step197) : Step198D := by
  intro G _ _ A c L E M hctx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L :=
    ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT,
      hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hE27 : Nat.card E = 27 := hctx.isE27.2
  have hA27 : Nat.card A = 27 := hD.card_eq
  have hne : E ≠ A := fun h => hctx.not_mem_partTwoT (h ▸ hctx.mem_partTwoT)
  have hdvd : Nat.card (E ⊓ A : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk27 : k ≠ 3 := by
    rintro rfl
    have h1 : E ⊓ A = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE27]; norm_num)
    have h2 : E ⊓ A = A := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hA27]; norm_num)
    exact hne (h1.symm.trans h2)
  suffices h9 : 9 ≤ Nat.card (E ⊓ A : Subgroup G) by
    have : k = 2 := by
      interval_cases k <;> simp_all
    rw [hk, this]
    norm_num
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData (h197 G A c L E M hctx)
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θH := aschbacherSolvableCore 3 H with hθH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  have hLAH : L ⊔ A ≤ H :=
    sup_le (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt) hD.A_le_normalizer_zpowers
  let ι : (L ⊔ A : Subgroup G) →* H := Subgroup.inclusion hLAH
  let φ : (L ⊔ A : Subgroup G) →* lBarA c L A :=
    ((QuotientGroup.mk' θH).comp ι).codRestrict (lBarA c L A) fun x =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hφv : ∀ x : (L ⊔ A : Subgroup G), ((φ x : lBarA c L A) : H ⧸ θH) =
      QuotientGroup.mk' θH ⟨(x : G), hLAH x.2⟩ := fun x => rfl
  have hker : Nat.Coprime 3 (Nat.card φ.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
    let j : φ.ker →* θH :=
      { toFun := fun x => ⟨ι x, by
          have h1 : ((φ x : lBarA c L A) : H ⧸ θH) = 1 := by rw [MonoidHom.mem_ker.mp x.2]; rfl
          rw [hφv, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
          exact h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun x y hxy => by
      have h1 : ((ι x : H) : G) = ((ι y : H) : G) := by
        have := congrArg (fun z : θH => ((z : H) : G)) hxy
        exact this
      exact Subtype.ext (Subtype.ext h1)
    exact h3.trans (Subgroup.card_dvd_of_injective j hj)
  have hELA : E ≤ L ⊔ A := hctx.le_sup.trans inf_le_left
  have hEA : E ≤ Subgroup.normalizer (A : Set G) := hctx.le_sup.trans inf_le_right
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := hctx.le_normalizer
  have hP3 : IsPGroup 3 (E ⊔ A : Subgroup G) :=
    hctx.isE27.isPGroup.to_sup_of_normal_right'
      (isE27_of_mem_partTwoE hctx.mem_partTwoE).isPGroup hEA
  have hinj := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup 3
    Nat.prime_three φ hker ((E ⊔ A).subgroupOf (L ⊔ A)) hP3.comap_subtype
  have hinjT : ∀ x y : (L ⊔ A : Subgroup G), (x : G) ∈ E ⊔ A → (y : G) ∈ E ⊔ A →
      φ x = φ y → x = y := fun x y hx hy h =>
    congrArg Subtype.val (hinj (a₁ := ⟨x, Subgroup.mem_subgroupOf.mpr hx⟩)
      (a₂ := ⟨y, Subgroup.mem_subgroupOf.mpr hy⟩) h)
  set AT := A.subgroupOf (L ⊔ A) with hAT
  set ET := E.subgroupOf (L ⊔ A) with hET
  have hinjA : Set.InjOn φ (AT : Set (L ⊔ A : Subgroup G)) := fun x hx y hy h =>
    hinjT x y (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)) h
  have hinjE : Set.InjOn φ (ET : Set (L ⊔ A : Subgroup G)) := fun x hx y hy h =>
    hinjT x y (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy)) h
  have hAb27 : Nat.card (AT.map φ) = 27 := by
    rw [card_map_of_injOn φ hinjA, ← hA27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hEb27 : Nat.card (ET.map φ) = 27 := by
    rw [card_map_of_injOn φ hinjE, ← hE27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hELA).toEquiv
  have hAbe : CFSG.Assembly.IsElemAbelian 3 (AT.map φ) :=
    isElemAbelian_map (isElemAbelian_subgroupOf hD.isElemAbelian _) φ
  have hEbe : CFSG.Assembly.IsElemAbelian 3 (ET.map φ) :=
    isElemAbelian_map (isElemAbelian_subgroupOf hctx.isE27.1 _) φ
  have hAbEb := map_le_normalizer_map φ (subgroupOf_le_normalizer hAE (L ⊔ A))
  have hEbAb := map_le_normalizer_map φ (subgroupOf_le_normalizer hEA (L ⊔ A))
  have hcent : ∀ x : (L ⊔ A : Subgroup G), (x : G) ∈ Sec4.thetaQuotCentralizer L →
      φ x ∈ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) := by
    intro x hx
    rw [hL₀, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    obtain ⟨-, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
    have h1 := hxl l hlL
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt,
      inSubgroup_theta_centralizer] at h1
    obtain ⟨t, ht, hte⟩ := h1.2.2
    set x' : H := ⟨(x : G), hLAH x.2⟩ with hx'
    have h2 : l⁻¹ * (x' * l * x'⁻¹) ∈ θH := by
      have e : l⁻¹ * (x' * l * x'⁻¹) = t := Subtype.ext hte.symm
      rw [e]
      exact ht
    have h3 : QuotientGroup.mk' θH (l⁻¹ * (x' * l * x'⁻¹)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    apply Subtype.ext
    change (y : H ⧸ θH) * QuotientGroup.mk' θH x' = QuotientGroup.mk' θH x' * (y : H ⧸ θH)
    rw [← hly]
    calc QuotientGroup.mk' θH l * QuotientGroup.mk' θH x' =
        QuotientGroup.mk' θH l * ((QuotientGroup.mk' θH l)⁻¹ * (QuotientGroup.mk' θH x' *
          QuotientGroup.mk' θH l * (QuotientGroup.mk' θH x')⁻¹)) * QuotientGroup.mk' θH x' := by
          rw [h3, mul_one]
      _ = QuotientGroup.mk' θH x' * QuotientGroup.mk' θH l := by group
  have hCE9 : 9 ≤ Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
    nine_le_card_of_not_isCyclic (fun x hx => hctx.isE27.1.2 x hx.1)
      hctx.centralizer_noncyclic
  have hEC : 9 ≤ Nat.card (ET.map φ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :
      Subgroup (lBarA c L A)) := by
    refine hCE9.trans (Nat.card_le_card_of_injective
      (fun x : (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) =>
        (⟨φ ⟨(x : G), hELA x.2.1⟩, ⟨⟨(x : G), hELA x.2.1⟩, Subgroup.mem_subgroupOf.mpr x.2.1,
          rfl⟩, hcent _ x.2.2⟩ : (ET.map φ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :
            Subgroup (lBarA c L A)))) ?_)
    intro x y hxy
    have h1 := hinjT ⟨(x : G), hELA x.2.1⟩ ⟨(y : G), hELA y.2.1⟩ (Subgroup.mem_sup_left x.2.1)
      (Subgroup.mem_sup_left y.2.1) (congrArg Subtype.val hxy)
    exact Subtype.ext (congrArg (fun z : (L ⊔ A : Subgroup G) => (z : G)) h1)
  have hcA : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ ∈ AT.map φ :=
    ⟨⟨c, Subgroup.mem_sup_right hD.mem_A⟩, Subgroup.mem_subgroupOf.mpr hD.mem_A, rfl⟩
  have hcZ : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ ∈ Subgroup.center (lBarA c L A) :=
    mkC_mem_center hD
  have hc1 : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ ≠ 1 := mkC_ne_one hD
  have h9 := nine_le_card_inf D hAbe hAb27 hEbe hEb27 hAbEb hEbAb hEC hcA
    (Subgroup.center_le_centralizer _ hcZ) hc1
  refine h9.trans (Nat.card_le_card_of_surjective
    (fun x : (E ⊓ A : Subgroup G) => (⟨φ ⟨(x : G), Subgroup.mem_sup_right x.2.2⟩,
      ⟨⟨(x : G), Subgroup.mem_sup_right x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2.2, rfl⟩,
      ⟨⟨(x : G), Subgroup.mem_sup_right x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2.1, rfl⟩⟩ :
        (AT.map φ ⊓ ET.map φ : Subgroup (lBarA c L A)))) ?_)
  rintro ⟨z, ⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
  have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
  have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
  have hxy : y = x := hinjT y x (Subgroup.mem_sup_left hyE) (Subgroup.mem_sup_right hxA) hyx
  refine ⟨⟨(x : G), hxy ▸ hyE, hxA⟩, Subtype.ext ?_⟩
  rfl

end CFSG.RankThree.PartTwo.Sec19
