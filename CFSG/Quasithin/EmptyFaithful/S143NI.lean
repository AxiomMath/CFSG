module

public import CFSG.Quasithin.EmptyFaithful.S143NH
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

section Coset

variable {G : Type*} [Group G]

theorem mem_of_not_mem_of_relIndex_two {H K : Subgroup G} (h : H.relIndex K = 2) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x * y⁻¹ ∈ H := by
  obtain ⟨a₀, ha₀, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp h
  have h1 : x * a₀ ∈ H := by
    rcases hxor x hx with ⟨h1, -⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hxH
  have h2 : y * a₀ ∈ H := by
    rcases hxor y hy with ⟨h1, -⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hyH
  have := H.mul_mem h1 (H.inv_mem h2)
  simpa [mul_assoc] using this

end Coset

section TwoElt

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_two_element {A Kd : Subgroup G} {y₅ o : G} (hA : Nat.card A = 16)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKdN : Kd ≤ Subgroup.normalizer (A : Set G))
    (hy₅ : y₅ ∈ Kd) (hy₅o : orderOf y₅ = 5)
    (hfix : ∀ a ∈ A, y₅ * a * y₅⁻¹ = a → a = 1) {m : ℕ} (ho : o ^ 2 ^ m = 1)
    (hoN : o ∈ Subgroup.normalizer (A : Set G)) (hcomm : ∀ k ∈ Kd, k * o * k⁻¹ * o⁻¹ ∈ A) :
    ∀ a ∈ A, o * a = a * o := by
  classical
  set B : Subgroup G := A ⊓ Subgroup.centralizer ({o} : Set G) with hB
  have hshift : ∀ a₀ ∈ A, ∀ w ∈ A, (a₀ * o) * w = w * (a₀ * o) → o * w = w * o := by
    intro a₀ ha₀ w hw h
    have hw' : o * w * o⁻¹ ∈ A := conj_mem_of_mem_normalizer hoN hw
    have h1 : a₀ * (o * w * o⁻¹) = w * a₀ := by
      calc a₀ * (o * w * o⁻¹) = ((a₀ * o) * w) * o⁻¹ := by group
        _ = (w * (a₀ * o)) * o⁻¹ := by rw [h]
        _ = w * a₀ := by group
    have h2 : (o * w * o⁻¹) * a₀ = a₀ * (o * w * o⁻¹) := (hAab _ hw' a₀ ha₀)
    have h3 : (o * w * o⁻¹) * a₀ = w * a₀ := by rw [h2, h1]
    have h4 : o * w * o⁻¹ = w := mul_right_cancel h3
    calc o * w = (o * w * o⁻¹) * o := by group
      _ = w * o := by rw [h4]
  have hshift' : ∀ a₀ ∈ A, ∀ w ∈ A, o * w = w * o → (a₀ * o) * w = w * (a₀ * o) := by
    intro a₀ ha₀ w hw h
    calc (a₀ * o) * w = a₀ * (o * w) := by group
      _ = a₀ * (w * o) := by rw [h]
      _ = (a₀ * w) * o := by group
      _ = (w * a₀) * o := by rw [hAab a₀ ha₀ w hw]
      _ = w * (a₀ * o) := by group
  have hBinv : ∀ b ∈ B, y₅ * b * y₅⁻¹ ∈ B := by
    intro b hb
    have hbA : b ∈ A := hb.1
    have hbo : o * b = b * o := Subgroup.mem_centralizer_iff.mp hb.2 o rfl
    refine ⟨conj_mem_of_mem_normalizer (hKdN hy₅) hbA, Subgroup.mem_centralizer_iff.mpr
      fun h' hh' => ?_⟩
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    have ha₀A : y₅ * h' * y₅⁻¹ * h'⁻¹ ∈ A := hcomm y₅ hy₅
    have hyo : y₅ * h' * y₅⁻¹ = (y₅ * h' * y₅⁻¹ * h'⁻¹) * h' := by group
    have hbA' : y₅ * b * y₅⁻¹ ∈ A := conj_mem_of_mem_normalizer (hKdN hy₅) hbA
    have hc1 : ((y₅ * h' * y₅⁻¹ * h'⁻¹) * h') * (y₅ * b * y₅⁻¹) =
        (y₅ * b * y₅⁻¹) * ((y₅ * h' * y₅⁻¹ * h'⁻¹) * h') := by
      rw [← hyo]
      calc y₅ * h' * y₅⁻¹ * (y₅ * b * y₅⁻¹) = y₅ * (h' * b) * y₅⁻¹ := by group
        _ = y₅ * (b * h') * y₅⁻¹ := by rw [hbo]
        _ = (y₅ * b * y₅⁻¹) * (y₅ * h' * y₅⁻¹) := by group
    exact hshift _ ha₀A _ hbA' hc1
  have hBA : B ≤ A := inf_le_left
  have hfp : ∃ b ∈ A, b ≠ 1 ∧ o * b = b * o := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let f : Function.End ↥A := fun b => ⟨o * b * o⁻¹, conj_mem_of_mem_normalizer hoN b.2⟩
    have key : ∀ n : ℕ, ∀ b : ↥A, (((f ^ n) b : ↥A) : G) = o ^ n * b * (o ^ n)⁻¹ := by
      intro n
      induction n with
      | zero =>
        intro b
        have : (f ^ 0) b = b := rfl
        rw [this]
        simp
      | succ n ih =>
        intro b
        rw [pow_succ]
        show (((f ^ n) (f b) : ↥A) : G) = _
        rw [ih]
        show o ^ n * (o * ↑b * o⁻¹) * (o ^ n)⁻¹ = _
        rw [pow_succ]
        group
    have hf : f ^ 2 ^ m = 1 := by
      funext b
      apply Subtype.ext
      rw [key, ho]
      have h1 : (1 : Function.End ↥A) b = b := rfl
      rw [h1]
      simp
    have : Fintype ↥A := Fintype.ofFinite _
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := m) hf
    have hcard : Fintype.card ↥A = 16 := by rw [← Nat.card_eq_fintype_card]; exact hA
    by_contra hno
    push Not at hno
    have hfixcard : Fintype.card (Function.fixedPoints f) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, by
        show f 1 = 1
        apply Subtype.ext
        simp [f]⟩, fun ⟨b, hb⟩ => ?_⟩
      apply Subtype.ext
      by_contra hb1
      have hb1' : (b : G) ≠ 1 := fun e => hb1 (Subtype.ext e)
      have hb' : (f b : ↥A) = b := hb
      have h1 : o * (b : G) * o⁻¹ = b := congrArg Subtype.val hb'
      apply hno b b.2 hb1'
      calc o * (b : G) = (o * b * o⁻¹) * o := by group
        _ = b * o := by rw [h1]
    rw [hcard, hfixcard] at hmod
    exact absurd hmod (by decide)
  obtain ⟨b, hbA, hb1, hbo⟩ := hfp
  have hBne : B ≠ ⊥ := by
    intro hbot
    have : b ∈ B := ⟨hbA, Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact hbo⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hb1 this
  rcases eq_bot_or_eq_of_order_five hA hBA hy₅o hBinv hfix with h0 | h1
  · exact absurd h0 hBne
  · intro a ha
    have : a ∈ B := by rw [h1]; exact ha
    exact Subgroup.mem_centralizer_iff.mp this.2 o rfl

end TwoElt


section TdRq

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVr : ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2) {p : Fin 6} (hps : s p ≠ p)
  (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
  (hrq : (rOf T M ⊔ qOf T).relIndex T = 2)
  (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t)

include hS htT htRQ hM hP hVr hδD hδ hδA hps hcoc hrq hAAt

theorem tdOf_le_rq : tdOf T δ ≤ rOf T M ⊔ qOf T := by
  intro t' ht'
  by_contra ht'RQ
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  have ht'T : t' ∈ T := ht'.1
  have ht'δ : t' * δ = δ * t' := (Subgroup.mem_centralizer_iff.mp ht'.2 δ rfl).symm
  have hρ : t' * t⁻¹ ∈ rOf T M ⊔ qOf T :=
    mem_of_not_mem_of_relIndex_two hrq ht'T htT ht'RQ htRQ
  have hρN : t' * t⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (c.isSylowTwoOf_rq_normalizer_Ac hrW hrV hr2).1 hρ
  have hδt' : δ * t'⁻¹ = t'⁻¹ * δ := by
    calc δ * t'⁻¹ = t'⁻¹ * (t' * δ) * t'⁻¹ := by group
      _ = t'⁻¹ * (δ * t') * t'⁻¹ := by rw [ht'δ]
      _ = t'⁻¹ * δ := by group
  have hle : rOf T M ≤ Subgroup.centralizer ({δ} : Set G) := by
    rw [hAAt]
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact (Subgroup.mem_centralizer_iff.mp hδ w hw).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      have hwA : t * w * t⁻¹ ∈ c.Ac hrW hrV hr2 := mem_conjSubgroup_iff.mp hw
      have ha₁ : t' * w * t'⁻¹ ∈ c.Ac hrW hrV hr2 := by
        have h1 := conj_mem_of_mem_normalizer hρN hwA
        have e : t' * w * t'⁻¹ = (t' * t⁻¹) * (t * w * t⁻¹) * (t' * t⁻¹)⁻¹ := by group
        rw [e]
        exact h1
      have h2 := Subgroup.mem_centralizer_iff.mp hδ _ ha₁
      calc h' * w = (h' * t'⁻¹) * (t' * w * t'⁻¹) * t' := by group
        _ = (t'⁻¹ * h') * (t' * w * t'⁻¹) * t' := by rw [hδt']
        _ = t'⁻¹ * (h' * (t' * w * t'⁻¹)) * t' := by group
        _ = t'⁻¹ * ((t' * w * t'⁻¹) * h') * t' := by rw [← h2]
        _ = (t'⁻¹ * (t' * w * t'⁻¹)) * (h' * t') := by group
        _ = (t'⁻¹ * (t' * w * t'⁻¹)) * (t' * h') := by rw [ht'δ]
        _ = w * h' := by group
  obtain ⟨ρ, hρR, hρnc⟩ := exists_rho_not_centralize hS htT htRQ hM hP hVr hδD hδ hδA hps hcoc
  exact hρnc (Subgroup.mem_centralizer_iff.mp (hle hρR) δ rfl).symm

end TdRq

section Hstar

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.card_OTwoQuot_mcOf : Nat.card (OTwoQuot (mcOf T)) = 72 := by
  have hker : c.actK.ker = CFSG.Open.pCore 2 ↥(mcOf T) := by
    apply Subgroup.map_injective (mcOf T).subtype_injective
    rw [c.actK_ker_map]
    rfl
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker.symm).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange c.actK).toEquiv]
  exact c.card_range_actK

theorem Counter.exists_card_nine_le_image :
    ∃ P : Subgroup (OTwoQuot (mcOf T)), Nat.card P = 9 ∧
      P ≤ imageOTwoQuot (mcOf T) (oTwoUpper (mcOf T)) := by
  have h9 : 3 ^ 2 ∣ Nat.card (OTwoQuot (mcOf T)) := by
    rw [c.card_OTwoQuot_mcOf]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  refine ⟨P, by simpa using hP, fun x hx => ?_⟩
  have hodd : Odd (orderOf x) := by
    have hdvd : orderOf x ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard P hx
      rwa [show Nat.card ↥P = 9 by simpa using hP] at this
    exact Odd.of_dvd_nat (by decide) hdvd
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (mcOf T) h.2
  have hcop : Nat.Coprime (2 ^ k) (orderOf (QuotientGroup.mk h : OTwoQuot (mcOf T))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hmem : (QuotientGroup.mk h : OTwoQuot (mcOf T)) ^ 2 ^ k ∈
      imageOTwoQuot (mcOf T) (oTwoUpper (mcOf T)) := by
    refine ⟨h ^ 2 ^ k, ?_, ?_⟩
    · exact hk
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_pow]
  have hz := A4.mem_zpowers_pow_of_coprime hcop
  exact (Subgroup.zpowers_le.mpr hmem) hz

end Hstar

section PCore

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2)
  (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))
  (hc18c : Concl18c T (c.Ac hrW hrV hr2))

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hc18c

theorem not_le_pCoreOf_gd :
    ¬ c.Ac hrW hrV hr2 ≤ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hAO
  set A := c.Ac hrW hrV hr2 with hAdef
  set H := mcOf T with hHdef
  set O := pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) with hO
  have hO2H : oTwoUpper H ≤ Subgroup.centralizer ({δ} : Set G) :=
    oTwoUpper_mcOf_le_centralizer hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb
  have hOnorm : Subgroup.centralizer ({δ} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hAH : A ≤ H := by
    have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
    have hTH : T ≤ H := c.h1281.almostSpecialHyp_g1.T_le_H
    exact (c.Ac_le_rOf hrW hrV hr2).trans (le_sup_left.trans (hRQT.trans hTH))
  have hsub : IsSubnormal (oTwoUpper H) H :=
    A4.subnormal_of_normal (oTwoUpper_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H))
  have hN1 : ∀ w ∈ oTwoUpper H, ∀ n ∈ O ⊓ oTwoUpper H, w * n * w⁻¹ ∈ O ⊓ oTwoUpper H := by
    intro w hw n hn
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hOnorm (hO2H hw)) n).mp hn.1, ?_⟩
    exact (oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem hw hn.2) ((oTwoUpper H).inv_mem hw)
  have hN1le : O ⊓ oTwoUpper H ≤ pCoreOf 2 (oTwoUpper H) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ((pCoreOf_isPGroup 2 _).to_inf_left)
    intro w hw
    refine mem_normalizer_of_conj_mem (fun n hn => hN1 w hw n hn) (fun n hn => ?_)
    have := hN1 w⁻¹ ((oTwoUpper H).inv_mem hw) n hn
    simpa using this
  have hcomm : ∀ a' ∈ A, ∀ o ∈ oTwoUpper H, a' * o * a'⁻¹ * o⁻¹ ∈ pCoreOf 2 H := by
    intro a' ha' o ho
    have hmem : a' * o * a'⁻¹ * o⁻¹ ∈ O ⊓ oTwoUpper H := by
      refine ⟨?_, ?_⟩
      · have h1 : o * a'⁻¹ * o⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hOnorm (hO2H ho)) a'⁻¹).mp (O.inv_mem (hAO ha'))
        have h2 := O.mul_mem (hAO ha') h1
        simpa [mul_assoc] using h2
      · have h1 : a' * o * a'⁻¹ ∈ oTwoUpper H :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hAH ha')) o).mp ho
        exact (oTwoUpper H).mul_mem h1 ((oTwoUpper H).inv_mem ho)
    exact A4.pCoreOf_le_of_subnormal 2 hsub (hN1le hmem)
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  have hle : imageOTwoQuot H (oTwoUpper H) ≤
      imageOTwoQuot H (H ⊓ Subgroup.normalizer (A : Set G)) := by
    rw [hc18c.nh_star]
    rintro _ ⟨o, ho, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    obtain ⟨a', ha', rfl⟩ := hw
    have hq : a' * o * a'⁻¹ * o⁻¹ ∈ CFSG.Open.pCore 2 ↥H := by
      refine (mem_pCore_iff _).mpr ?_
      have := hcomm (a' : G) (Subgroup.mem_subgroupOf.mp ha') (o : G)
        (Subgroup.mem_subgroupOf.mp ho)
      simpa using this
    have h1 : ⁅π a', π o⁆ = 1 := by
      rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hq
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  obtain ⟨P, hP9, hPle⟩ := c.exists_card_nine_le_image
  have h9 : 9 ∣ Nat.card ↥(imageOTwoQuot H (H ⊓ Subgroup.normalizer (A : Set G))) := by
    have h1 := Subgroup.card_dvd_of_le hPle
    have h2 := Subgroup.card_dvd_of_le hle
    rw [hP9] at h1
    exact h1.trans h2
  obtain ⟨e⟩ := hc18c.nh_iso
  have h12 : Nat.card ↥(imageOTwoQuot H (H ⊓ Subgroup.normalizer (A : Set G))) = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_perm, ZMod.card, Nat.factorial]
  rw [h12] at h9
  omega

end PCore

section PCoreGd

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hVr : ∀ σ ∈ Vr, ∃ ρ' ∈ rOf T M, mm cm (matOf6 σ) = mm (cmat z a r r1 ρ') cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2) {p : Fin 6} (hps : s p ≠ p)
  (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)
  {y₅ : G} (hy₅ : y₅ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) (hy₅o : orderOf y₅ = 5)
  (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))
  (hc18c : Concl18c T (c.Ac hrW hrV hr2))
  (hrq : (rOf T M ⊔ qOf T).relIndex T = 2)
  (hAAt : rOf T M = c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t)
  (hNAK : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
    Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G))
  (hNA : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
    kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M)
  (hnc : ∀ x' : G, x' * z * x'⁻¹ ≠ δ) (hnc' : ∀ x' : G, x' * z * x'⁻¹ ≠ z * δ)

include hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o in
theorem fix_A
    : ∀ a' ∈ c.Ac hrW hrV hr2, y₅ * a' * y₅⁻¹ = a' → a' = 1 := by
  intro a' ha' h
  have hB := blockData_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
  have := hB.fix ⟨a', A_le_kdOf hS hM hδD hδ hδA hcoc ha'⟩ (Subgroup.mem_subgroupOf.mpr ha')
    (Subtype.ext h)
  exact congrArg Subtype.val this

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA hcoc hy₅ hy₅o hemb hc18c in
theorem inf_A_pCoreOf_gd :
    c.Ac hrW hrV hr2 ⊓ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) = ⊥ := by
  have hkdG : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ Subgroup.centralizer ({δ} : Set G) :=
    inf_le_right
  have hOnorm : Subgroup.centralizer ({δ} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hkdN : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤
      Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := kdOf_le_normalizer
  have hyB : ∀ b ∈ c.Ac hrW hrV hr2 ⊓ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)),
      y₅ * b * y₅⁻¹ ∈ c.Ac hrW hrV hr2 ⊓ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := by
    intro b hb
    exact ⟨conj_mem_of_mem_normalizer (hkdN hy₅) hb.1,
      (Subgroup.mem_normalizer_iff.mp (hOnorm (hkdG hy₅)) b).mp hb.2⟩
  rcases eq_bot_or_eq_of_order_five (c.card_Ac hrW hrV hr2) inf_le_left hy₅o hyB
    (fix_A hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o) with h0 | h1
  · exact h0
  · exfalso
    apply not_le_pCoreOf_gd hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hc18c
    rw [← h1]
    exact inf_le_right

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hy₅ hy₅o hemb hrq hAAt hNAK hnc hnc' in
theorem pCoreOf_gd_le_centralizer :
    pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) ≤
      Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := hS.basis
  have hSyl := isSylowTwoOf_tdOf_gd hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hnc hnc'
  have hOT : pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) ≤ tdOf T δ :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
  have hTdS : tdOf T δ ≤ sdOf T M δ := fun w hw =>
    ⟨tdOf_le_rq hS htT htRQ hM hP hVr hδD hδ hδA hps hcoc hrq hAAt hw, hw.2⟩
  have hSN := sd_le_normalizer_kd c hNAK (δ := δ)
  have hkdG : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ Subgroup.centralizer ({δ} : Set G) :=
    inf_le_right
  have hOnorm : Subgroup.centralizer ({δ} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hAkd := A_le_kdOf hS hM hδD hδ hδA hcoc
  have hkdN : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤
      Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := kdOf_le_normalizer
  have hA2 : IsPGroup 2 ↥(c.Ac hrW hrV hr2) :=
    c.hyp.sylow.1.to_le ((c.Ac_le_rOf hrW hrV hr2).trans (rOf_le_T_of_hyp c.h1281))
  have hpc : pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) = c.Ac hrW hrV hr2 :=
    le_antisymm (kd_pCore_le hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o)
      (le_pCoreOf_of_le_normalizer 2 hAkd hkdN hA2)
  have hOKd : pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) ⊓
      kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤
      pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ((pCoreOf_isPGroup 2 _).to_inf_left)
    intro k hk
    have key : ∀ k' ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ, ∀ w ∈ pCoreOf 2
        (Subgroup.centralizer ({δ} : Set G)) ⊓ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ,
        k' * w * k'⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) ⊓
          kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := fun k' hk' w hw =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hOnorm (hkdG hk')) w).mp hw.1,
        (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).mul_mem
          ((kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).mul_mem hk' hw.2)
          ((kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).inv_mem hk')⟩
    refine mem_normalizer_of_conj_mem (fun w hw => key k hk w hw) (fun w hw => ?_)
    have := key k⁻¹ ((kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).inv_mem hk) w hw
    simpa using this
  intro o ho
  have hoKd : o ∈ Subgroup.normalizer (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ : Set G) :=
    hSN (hTdS (hOT ho))
  have hoNA : o ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
    have := normalizer_le_normalizer_pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) hoKd
    rwa [hpc] at this
  have hcomm : ∀ k ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ, k * o * k⁻¹ * o⁻¹ ∈ c.Ac hrW hrV hr2 := by
    intro k hk
    have h1 : o * k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) ⊓
        kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
      refine ⟨?_, ?_⟩
      · have h2 : k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) :=
          (Subgroup.mem_normalizer_iff.mp (hOnorm (hkdG hk)) o⁻¹).mp
            ((pCoreOf 2 (Subgroup.centralizer ({δ} : Set G))).inv_mem ho)
        have h3 := (pCoreOf 2 (Subgroup.centralizer ({δ} : Set G))).mul_mem ho h2
        have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
        rw [e]
        exact h3
      · exact (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).mul_mem
          ((Subgroup.mem_normalizer_iff.mp hoKd k).mp hk)
          ((kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).inv_mem hk)
    have h4 : o * k * o⁻¹ * k⁻¹ ∈ c.Ac hrW hrV hr2 := hpc ▸ hOKd h1
    have h5 := (c.Ac hrW hrV hr2).inv_mem h4
    have e : (o * k * o⁻¹ * k⁻¹)⁻¹ = k * o * k⁻¹ * o⁻¹ := by group
    rwa [e] at h5
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (Subgroup.centralizer ({δ} : Set G)) ⟨o, ho⟩
  have ho2 : o ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hcent := centralizes_of_two_element (c.card_Ac hrW hrV hr2)
    (fun u hu w hw => hB.comm u hu w hw) hkdN hy₅ hy₅o
    (fix_A hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o) ho2 hoNA hcomm
  exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => (hcent a' ha').symm

include hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hy₅ hy₅o hemb hc18c hrq hAAt hNAK hNA hnc
  hnc' in
theorem pCoreOf_gd_eq :
    pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) = Subgroup.zpowers δ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers δ) := by
    have hord : orderOf δ = 2 := orderOf_eq_prime (by rw [← pow_two] at hδ2; exact hδ2) hδ1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  have hδO : δ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := by
    have hle : Subgroup.zpowers δ ≤ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) :=
      le_pCoreOf_of_le_normalizer 2
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
          rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl))
        (centralizer_singleton_le_normalizer_zpowers δ) hzp
    exact hle (Subgroup.mem_zpowers δ)
  have hinf := inf_A_pCoreOf_gd hS htT htRQ hM hP hVl hC1 hδD hδ hδA hcoc hy₅ hy₅o hemb hc18c
  have hOΓ := pCoreOf_gd_le_centralizer hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hy₅ hy₅o
    hemb hrq hAAt hNAK hnc hnc'
  apply le_antisymm
  · intro o ho
    obtain ⟨a', ha', δ', hδ'D, hδ'Γ, rfl⟩ :=
      exists_decomp_of_mem_centralizer hS hM hP.conf htT htRQ hNA (hOΓ ho)
    have hz2 : z ∈ c.Ac hrW hrV hr2 := hS.z_A
    have hO : ∀ w ∈ c.Ac hrW hrV hr2, w * δ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) →
        w = 1 := by
      intro w hw hwδ
      have : w ∈ c.Ac hrW hrV hr2 ⊓ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := by
        refine ⟨hw, ?_⟩
        have := (pCoreOf 2 (Subgroup.centralizer ({δ} : Set G))).mul_mem hwδ
          ((pCoreOf 2 (Subgroup.centralizer ({δ} : Set G))).inv_mem hδO)
        simpa using this
      rw [hinf, Subgroup.mem_bot] at this
      exact this
    have hO' : ∀ w ∈ c.Ac hrW hrV hr2, w ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) →
        w = 1 := by
      intro w hw hwO
      have : w ∈ c.Ac hrW hrV hr2 ⊓ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := ⟨hw, hwO⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact this
    rcases D0_cases hS htT htRQ hM hP hVl hC1 hδD hδ hδA hδ'D hδ'Γ with e | e | e | e
    · rw [e] at ho ⊢
      have := hO' a' ha' (by simpa using ho)
      rw [this]
      simp
    · rw [e] at ho ⊢
      have := hO' (a' * z) ((c.Ac hrW hrV hr2).mul_mem ha' hz2) ho
      rw [this]
      simp
    · rw [e] at ho ⊢
      have := hO a' ha' ho
      rw [this]
      simp [Subgroup.mem_zpowers]
    · rw [e] at ho ⊢
      have h1 : a' * z ∈ c.Ac hrW hrV hr2 := (c.Ac hrW hrV hr2).mul_mem ha' hz2
      have h2 : (a' * z) * δ ∈ pCoreOf 2 (Subgroup.centralizer ({δ} : Set G)) := by
        have e' : (a' * z) * δ = a' * (z * δ) := by group
        rw [e']
        exact ho
      have := hO (a' * z) h1 h2
      have e'' : a' * (z * δ) = (a' * z) * δ := by group
      rw [e'', this]
      simp [Subgroup.mem_zpowers]
  · exact Subgroup.zpowers_le.mpr hδO

end PCoreGd




end S143

end CFSG.Quasithin
