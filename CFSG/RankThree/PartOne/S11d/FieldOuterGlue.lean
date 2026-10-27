module

public import CFSG.RankThree.PartOne.S11d.OutTheta
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.RankThree.PartOne.S11d.FourClaimAux

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)

namespace OutTheta

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizing_lift {p : ℕ} (hp : p.Prime) {I A : Subgroup G}
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) {Γ : Type} [Group Γ] (φ : ↥I →* Γ)
    (ψ : ↥A →* Γ) (hker : ∀ i : ↥I, φ i = 1 ↔ i ∈ aschbacherSolvableCore p ↥I)
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    {v : G} (hvA : v ∈ A) (hvp : v ^ p = 1) (i₀ : ↥I)
    (hcomm : ψ ⟨v, hvA⟩ * φ i₀ = φ i₀ * ψ ⟨v, hvA⟩) :
    ∃ i : ↥I, φ i = φ i₀ ∧ v * (i : G) = (i : G) * v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set n : MulAut ↥I := I.normalizerMonoidHom ⟨v, hAI hvA⟩ with hn
  have hnp : n ^ p = 1 := by
    rw [hn, ← map_pow]
    have : (⟨v, hAI hvA⟩ : Subgroup.normalizer (I : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hvp)
    rw [this, map_one]
  have hnφ : ∀ i : ↥I, φ (n i) = ψ ⟨v, hvA⟩ * φ i * (ψ ⟨v, hvA⟩)⁻¹ := fun i =>
    (hcompat ⟨v, hvA⟩ i).symm
  let S : Type := {i : ↥I // φ i = φ i₀}
  have hnS : ∀ s : S, φ (n s.1) = φ i₀ := by
    intro s
    rw [hnφ, s.2]
    exact mul_inv_eq_iff_eq_mul.mpr hcomm
  let f : Function.End S := fun s => ⟨n s.1, hnS s⟩
  have hfp : f ^ p ^ 1 = 1 := by
    have key : ∀ k : ℕ, ∀ s : S, ((f ^ k) s).1 = (n ^ k) s.1 := by
      intro k
      induction k with
      | zero => intro s; rfl
      | succ k ih =>
        intro s
        rw [pow_succ, pow_succ]
        change ((f ^ k) (f s)).1 = (n ^ k) (n s.1)
        exact ih (f s)
    funext s
    apply Subtype.ext
    have h1 := key (p ^ 1) s
    rw [h1, pow_one, hnp]
    rfl
  let _ : Fintype S := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := S) hfp
  have hSker : Nat.card S = Nat.card φ.ker := by
    refine Nat.card_congr
      { toFun := fun s => ⟨i₀⁻¹ * s.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, s.2, inv_mul_cancel]⟩
        invFun := fun k => ⟨i₀ * k.1, by
          rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]⟩
        left_inv := fun s => by apply Subtype.ext; simp
        right_inv := fun k => by apply Subtype.ext; simp }
  have hkerθ : φ.ker = aschbacherSolvableCore p ↥I := by
    ext i
    exact hker i
  have hSnd : ¬ p ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, hSker, hkerθ]
    exact (solvable_prime_complement_core_characterization (H := ↥I) hp).2.2.1
  have hfix : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hSnd ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨⟨s, hs⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hfix)
  have hs' : n s.1 = s.1 := congrArg Subtype.val hs
  refine ⟨s.1, s.2, ?_⟩
  have h2 : ((n s.1 : ↥I) : G) = v * (s.1 : G) * v⁻¹ := by
    rw [hn, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [hs'] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2.symm

theorem not_solvable_of_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have := hQ.1
  exact Group.IsPerfect.not_isSolvable Q

section Model

variable {p : ℕ} {I A : Subgroup G} (hAI : A ≤ Subgroup.normalizer (I : Set G)) {Γ : Type}
  [Group Γ] (φ : ↥I →* Γ) (ψ : ↥A →* Γ)

omit [Finite G] in
include hAI in
theorem range_psi_le_normalizer
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i)) :
    ψ.range ≤ Subgroup.normalizer (φ.range : Set Γ) := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, (hcompat a i).symm⟩
  · rintro ⟨i, hi⟩
    refine ⟨I.normalizerMonoidHom ⟨((a⁻¹ : ↥A) : G), hAI (a⁻¹).2⟩ i, ?_⟩
    rw [← hcompat a⁻¹ i, map_inv, hi]
    group

omit [Finite G] in
include hAI in
theorem mem_sup_centralizer_of_inner
    (hker : ∀ i : ↥I, φ i = 1 ↔ i ∈ aschbacherSolvableCore p ↥I)
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    {a : G} (haA : a ∈ A) (hinn : InnerOnTheta p I a) :
    ψ ⟨a, haA⟩ ∈ φ.range ⊔ Subgroup.centralizer (φ.range : Set Γ) := by
  obtain ⟨haN, q, hq⟩ := hinn
  obtain ⟨i₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hc : (φ i₀)⁻¹ * ψ ⟨a, haA⟩ ∈ Subgroup.centralizer (φ.range : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    have h1 : (QuotientGroup.mk (I.normalizerMonoidHom ⟨a, haN⟩ k) :
        ↥I ⧸ aschbacherSolvableCore p ↥I) =
        QuotientGroup.mk (i₀ * k * i₀⁻¹) := by
      have := congrArg (fun σ : MulAut (↥I ⧸ aschbacherSolvableCore p ↥I) =>
        σ (QuotientGroup.mk k)) hq
      simp only [MulAut.conj_apply, thetaQuotientConj_mk] at this
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at this
      exact this.symm
    have h2 : φ (I.normalizerMonoidHom ⟨a, haN⟩ k) = φ (i₀ * k * i₀⁻¹) := by
      rw [QuotientGroup.eq] at h1
      have h3 := (hker _).mpr h1
      rw [map_mul, map_inv] at h3
      exact (inv_mul_eq_one.mp h3)
    have h4 : ψ ⟨a, haA⟩ * φ k * (ψ ⟨a, haA⟩)⁻¹ = φ i₀ * φ k * (φ i₀)⁻¹ := by
      rw [hcompat ⟨a, haA⟩ k]
      rw [h2, map_mul, map_mul, map_inv]
    have h5 : ψ ⟨a, haA⟩ * φ k = φ i₀ * φ k * (φ i₀)⁻¹ * ψ ⟨a, haA⟩ := by
      rw [← h4]
      group
    calc φ k * ((φ i₀)⁻¹ * ψ ⟨a, haA⟩) = (φ i₀)⁻¹ * (φ i₀ * φ k * (φ i₀)⁻¹ * ψ ⟨a, haA⟩) := by
          group
      _ = (φ i₀)⁻¹ * (ψ ⟨a, haA⟩ * φ k) := by rw [h5]
      _ = (φ i₀)⁻¹ * ψ ⟨a, haA⟩ * φ k := by group
  have : ψ ⟨a, haA⟩ = φ i₀ * ((φ i₀)⁻¹ * ψ ⟨a, haA⟩) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ⟨i₀, rfl⟩ hc

abbrev imageOf (φ : ↥I →* Γ) (E : Subgroup G) (hEI : E ≤ I) : Subgroup Γ :=
  (φ.comp (Subgroup.inclusion hEI)).range

omit [Finite G] in
include hAI in
theorem psi_comm_phi
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    {v : G} (hvA : v ∈ A) (i : ↥I) (hvi : v * (i : G) = (i : G) * v) :
    ψ ⟨v, hvA⟩ * φ i = φ i * ψ ⟨v, hvA⟩ := by
  have h1 := hcompat ⟨v, hvA⟩ i
  have h2 : I.normalizerMonoidHom ⟨v, hAI hvA⟩ i = i := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr hvi
  rw [h2] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem isComponentOf_image (hp : p.Prime) [Finite Γ]
    (hker : ∀ i : ↥I, φ i = 1 ↔ i ∈ aschbacherSolvableCore p ↥I)
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    {v : G} (hvA : v ∈ A) (hvp : v ^ p = 1) {E : Subgroup G}
    (hE : IsComponentOf (I ⊓ Subgroup.centralizer ({v} : Set G)) E) :
    IsComponentOf (φ.range ⊓ Subgroup.centralizer ({ψ ⟨v, hvA⟩} : Set Γ))
      (imageOf φ E (hE.1.trans inf_le_left)) := by
  classical
  have hEI : E ≤ I := hE.1.trans inf_le_left
  set X : Subgroup G := I ⊓ Subgroup.centralizer ({v} : Set G) with hX
  set Y : Subgroup Γ := φ.range ⊓ Subgroup.centralizer ({ψ ⟨v, hvA⟩} : Set Γ) with hY
  set ε : ↥E →* Γ := φ.comp (Subgroup.inclusion hEI) with hε
  have hcentr : ∀ i : ↥I, (i : G) ∈ Subgroup.centralizer ({v} : Set G) →
      φ i ∈ Subgroup.centralizer ({ψ ⟨v, hvA⟩} : Set Γ) := by
    intro i hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (psi_comm_phi hAI φ ψ hcompat hvA i
      (Subgroup.mem_centralizer_singleton_iff.mp hi).symm).symm
  have hle : imageOf φ E hEI ≤ Y := by
    rintro _ ⟨e, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    exact hcentr ⟨(e : G), hEI e.2⟩ (hE.1 e.2).2
  have hnontriv : ∃ e : ↥E, ε e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply not_solvable_of_quasisimple hE.2.1
    have hsolv : Group.IsSolvable ↥(aschbacherSolvableCore p ↥I) :=
      (solvable_prime_complement_core_characterization (H := ↥I) hp).1
    let f : ↥E →* ↥(aschbacherSolvableCore p ↥I) :=
      { toFun := fun e => ⟨⟨(e : G), hEI e.2⟩, (hker _).mp (hcon e)⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b h => Subtype.ext (by
      have h1 := congrArg (fun x : ↥(aschbacherSolvableCore p ↥I) => ((x : ↥I) : G)) h
      exact h1))
  have hkerε : ε.ker ≤ Subgroup.center ↥E :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hE.2.1 hnontriv
  have hq : CFSG.IsQuasisimple ↥(imageOf φ E hEI) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hE.2.1 ε.rangeRestrict
      ε.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hkerε)
  let ρ : ↥X →* ↥Y := (φ.comp (Subgroup.inclusion (inf_le_left : X ≤ I))).codRestrict Y (by
    intro x
    exact ⟨⟨_, rfl⟩, hcentr _ x.2.2⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hyJ, hyC⟩
    obtain ⟨i₀, rfl⟩ := hyJ
    have hcomm : ψ ⟨v, hvA⟩ * φ i₀ = φ i₀ * ψ ⟨v, hvA⟩ :=
      (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
    obtain ⟨i, hi, hiv⟩ := exists_centralizing_lift hp hAI φ ψ hker hcompat hvA hvp i₀ hcomm
    refine ⟨⟨(i : G), i.2, Subgroup.mem_centralizer_singleton_iff.mpr hiv.symm⟩, ?_⟩
    apply Subtype.ext
    exact hi
  have hsn : (imageOf φ E hEI |>.subgroupOf Y).IsSubnormal := by
    have h1 := Subgroup.IsSubnormal.map hρ hE.2.2
    convert h1 using 1
    ext y
    constructor
    · rintro ⟨e, he⟩
      refine ⟨⟨(e : G), hE.1 e.2⟩, e.2, ?_⟩
      apply Subtype.ext
      exact he
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), hx⟩, rfl⟩
  exact ⟨hle, hq, hsn⟩

omit [Finite G] in
include hAI in
theorem psi_mem_normalizer_image
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    {E : Subgroup G} (hEI : E ≤ I) {a : ↥A} (haE : (a : G) ∈ Subgroup.normalizer (E : Set G)) :
    ψ a ∈ Subgroup.normalizer (imageOf φ E hEI : Set Γ) := by
  have key : ∀ (b : ↥A), (b : G) ∈ Subgroup.normalizer (E : Set G) → ∀ y ∈ imageOf φ E hEI,
      ψ b * y * (ψ b)⁻¹ ∈ imageOf φ E hEI := by
    intro b hb y hy
    obtain ⟨e, rfl⟩ := hy
    refine ⟨⟨(b : G) * (e : G) * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hb e).mp e.2⟩, ?_⟩
    change φ ⟨(b : G) * (e : G) * (b : G)⁻¹, _⟩ = ψ b * φ ⟨(e : G), hEI e.2⟩ * (ψ b)⁻¹
    rw [hcompat b ⟨(e : G), hEI e.2⟩]
    congr 1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => key a haE y hy
  · intro hy
    have h2 := key a⁻¹ (by
      have : ((a⁻¹ : ↥A) : G) = (a : G)⁻¹ := rfl
      rw [this]
      exact (Subgroup.inv_mem_iff _).mpr haE) _ hy
    simpa [map_inv, mul_assoc] using h2

theorem fieldLike_image (hp : p.Prime) [Finite Γ]
    (hker : ∀ i : ↥I, φ i = 1 ↔ i ∈ aschbacherSolvableCore p ↥I)
    (hcompat : ∀ (a : ↥A) (i : ↥I), ψ a * φ i * (ψ a)⁻¹ =
      φ (I.normalizerMonoidHom ⟨(a : G), hAI a.2⟩ i))
    {u : G} (huA : u ∈ A) (hup : u ^ p = 1) {E : Subgroup G} (hEI : E ≤ I)
    (hEq : CFSG.IsQuasisimple ↥E) (huE : u ∈ Subgroup.normalizer (E : Set G))
    (hfl : FieldLike p u E) :
    FieldLike p (ψ ⟨u, huA⟩) (imageOf φ E hEI) := by
  classical
  set ε : ↥E →* Γ := φ.comp (Subgroup.inclusion hEI) with hε
  have hnorm := psi_mem_normalizer_image hAI φ ψ hcompat hEI (a := ⟨u, huA⟩) huE
  have hnontriv : ∃ e : ↥E, ε e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply not_solvable_of_quasisimple hEq
    have hsolv : Group.IsSolvable ↥(aschbacherSolvableCore p ↥I) :=
      (solvable_prime_complement_core_characterization (H := ↥I) hp).1
    let f : ↥E →* ↥(aschbacherSolvableCore p ↥I) :=
      { toFun := fun e => ⟨⟨(e : G), hEI e.2⟩, (hker _).mp (hcon e)⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b h => Subtype.ext (by
      have h1 := congrArg (fun x : ↥(aschbacherSolvableCore p ↥I) => ((x : ↥I) : G)) h
      exact h1))
  have hkerε : ε.ker ≤ Subgroup.center ↥E :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hEq hnontriv
  obtain ⟨hN, hnot, -, t, n, f, hf, hmodel⟩ := hfl
  refine ⟨hnorm, ?_, ?_, t, n, f, hf, ?_⟩
  ·
    intro hmem
    obtain ⟨x, hx, c, hc, hxc⟩ := exists_mul_of_mem_sup_centralizer' (J := imageOf φ E hEI)
      (x := ψ ⟨u, huA⟩) hmem
    obtain ⟨e₀, rfl⟩ := hx
    apply hnot
    have hw : ((e₀ : G))⁻¹ * u ∈ Subgroup.normalizer (E : Set G) :=
      mul_mem (inv_mem (Subgroup.le_normalizer e₀.2)) huE
    have hcomm : ∀ e ∈ E, ((e₀ : G))⁻¹ * u * e * (((e₀ : G))⁻¹ * u)⁻¹ * e⁻¹ ∈
        inSubgroup (aschbacherSolvableCore p) I := by
      intro e he
      set e' : ↥E := ⟨e, he⟩ with he'
      have h1 : φ (I.normalizerMonoidHom ⟨u, hAI huA⟩ ⟨e, hEI he⟩) =
          φ ⟨(e₀ : G) * e * (e₀ : G)⁻¹,
            mul_mem (mul_mem (hEI e₀.2) (hEI he)) (inv_mem (hEI e₀.2))⟩ := by
        rw [← hcompat ⟨u, huA⟩ ⟨e, hEI he⟩, hxc]
        have hc' : c * φ ⟨e, hEI he⟩ = φ ⟨e, hEI he⟩ * c :=
          (Subgroup.mem_centralizer_iff.mp hc (φ ⟨e, hEI he⟩) ⟨e', rfl⟩).symm
        calc ε e₀ * c * φ ⟨e, hEI he⟩ * (ε e₀ * c)⁻¹ =
            ε e₀ * (c * φ ⟨e, hEI he⟩ * c⁻¹) * (ε e₀)⁻¹ := by group
          _ = ε e₀ * φ ⟨e, hEI he⟩ * (ε e₀)⁻¹ := by
            rw [hc']; group
          _ = _ := by
            rw [hε]
            simp only [MonoidHom.comp_apply]
            rw [← map_inv, ← map_mul, ← map_mul]
            rfl
      set k₀ : ↥I := ⟨(e₀ : G), hEI e₀.2⟩ with hk₀
      set ee : ↥I := ⟨e, hEI he⟩ with hee
      set n : ↥I := I.normalizerMonoidHom ⟨u, hAI huA⟩ ee with hn
      have h2 : φ (k₀⁻¹ * (n * (k₀ * ee * k₀⁻¹)⁻¹) * k₀) = 1 := by
        have h3 : φ n = φ (k₀ * ee * k₀⁻¹) := h1
        simp only [map_mul, map_inv] at h3 ⊢
        rw [h3]
        group
      have hκ : ((e₀ : G))⁻¹ * u * e * (((e₀ : G))⁻¹ * u)⁻¹ * e⁻¹ =
          ((k₀⁻¹ * (n * (k₀ * ee * k₀⁻¹)⁻¹) * k₀ : ↥I) : G) := by
        simp only [hk₀, hee, hn, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        group
      rw [hκ]
      exact ⟨_, (hker _).mp h2, rfl⟩
    have hcent := centralizes_of_commutators_mem_theta hp hEq hEI hw hcomm
    have hwC : ((e₀ : G))⁻¹ * u ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh =>
        (mul_inv_eq_iff_eq_mul.mp (hcent h hh)).symm
    have : u = (e₀ : G) * (((e₀ : G))⁻¹ * u) := by group
    rw [this]
    exact Subgroup.mul_mem_sup e₀.2 hwC
  · have : (⟨u, huA⟩ : ↥A) ^ p = 1 := Subtype.ext (by simpa using hup)
    rw [← map_pow, this, map_one]
    exact Subgroup.one_mem _
  · have hsurj : Function.Surjective ε.rangeRestrict := ε.rangeRestrict_surjective
    have hkerR : ε.rangeRestrict.ker ≤ Subgroup.center ↥E := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hkerε
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hEq hsurj hkerR) hmodel

end Model

theorem model_quasisimple_catalog {p : ℕ} (hp : p.Prime)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hKP : CFSG.IsKProper G) {d : G} (hCtop : Subgroup.centralizer ({d} : Set G) ≠ ⊤)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p d) {Γ : Type} [Group Γ] [Finite Γ]
    (φ : ↥I →* Γ) (hker : ∀ i : ↥I, φ i = 1 ↔ i ∈ aschbacherSolvableCore p ↥I) :
    CFSG.IsQuasisimple ↥φ.range ∧ Catalog (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  classical
  have hkerφ : φ.ker = aschbacherSolvableCore p ↥I := by
    ext i
    exact hker i
  let eQJ : (↥I ⧸ aschbacherSolvableCore p ↥I) ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hQq : CFSG.IsQuasisimple (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  have hJq : CFSG.IsQuasisimple ↥φ.range := LocalCores.isQuasisimple_of_mulEquiv eQJ hQq
  refine ⟨hJq, ?_⟩
  have hcatQ := inCatalog_thetaQuotient hp hKP hCtop hI
  have hin : InCatalog (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
    let eT := QuotientGroup.congr (Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I))
      (Subgroup.center ↥φ.range) eQJ (Subgroup.map_center_eq eQJ)
    obtain ⟨i, ⟨ψ'⟩⟩ := hcatQ
    exact ⟨i, ⟨eT.symm.trans ψ'⟩⟩
  have hJs := hJq.2.1
  exact hbridge _ hJq.2.2 hin

end OutTheta

end CFSG.RankThree.PartOne
