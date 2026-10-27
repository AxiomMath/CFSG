module

public import CFSG.Quasithin.H13.L32A7S6a
public import CFSG.Quasithin.H13.L32A714w

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Square

variable {G : Type} [Group G]

theorem comm_eq_of_sq_mem_centralizer {U : Subgroup G} (hU2 : ∀ u ∈ U, u * u = 1) {a : G}
    (haU : a ∈ Subgroup.normalizer (U : Set G)) (ha4 : (a * a) * (a * a) = 1)
    (hsq : ∀ w ∈ U, (a * a) * w = w * (a * a) → a * w = w * a) : ∀ u ∈ U, a * u = u * a := by
  have hcU : ∀ x ∈ Subgroup.normalizer (U : Set G), ∀ w ∈ U, x * w * x⁻¹ * w⁻¹ ∈ U :=
    fun x hx w hw => mul_mem ((Subgroup.mem_normalizer_iff.mp hx w).mp hw) (inv_mem hw)
  have hc1 : ∀ x w : G, x * w * x⁻¹ * w⁻¹ = 1 → x * w = w * x := fun x w h => by
    calc x * w = (x * w * x⁻¹ * w⁻¹) * w * x := by group
      _ = w * x := by rw [h]; group
  have hI : ∀ x ∈ Subgroup.normalizer (U : Set G), ∀ w ∈ U,
      (x * x) * w * (x * x)⁻¹ * w⁻¹ =
        x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ := by
    intro x hx w hw
    rw [inv_eq_of_mul_eq_one_left (hU2 _ (hcU x hx w hw))]
    group
  have hsN : a * a ∈ Subgroup.normalizer (U : Set G) := mul_mem haU haU
  intro u hu
  have hvU := hcU a haU u hu
  have hrU := hcU (a * a) hsN u hu
  have h1 : (a * a) * ((a * a) * u * (a * a)⁻¹ * u⁻¹) * (a * a)⁻¹ *
      ((a * a) * u * (a * a)⁻¹ * u⁻¹)⁻¹ = 1 := by
    rw [← hI (a * a) hsN u hu, ha4]
    group
  have h2 := hsq _ hrU (hc1 _ _ h1)
  have h3 : (a * a) * (a * u * a⁻¹ * u⁻¹) * (a * a)⁻¹ * (a * u * a⁻¹ * u⁻¹)⁻¹ = 1 := by
    rw [hI a haU _ hvU, ← hI a haU u hu, h2]
    group
  have h4 := hsq _ hvU (hc1 _ _ h3)
  have h5 : (a * a) * u * (a * a)⁻¹ * u⁻¹ = 1 := by
    rw [hI a haU u hu, h4]
    group
  exact hsq u hu (hc1 _ _ h5)

end Square

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem conj_le_centralizer_of_ti {D : Subgroup G} (hTI : fusionIsTI D) (hD4 : Nat.card D = 4)
    (hV1D : fsuV1 T V ≤ D) (hDK : ∀ d ∈ D, ∀ k ∈ oTwoUpper H, d * k = k * d) {g : G}
    (hg : Quasithin.conjSub g D ≤ pCoreOf 2 (l1 T L V ⊔ T)) :
    Quasithin.conjSub g D ≤ Subgroup.centralizer (fsuU T V : Set G) := by
  classical
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hUe := isElemAbelian_fsuU_of E.S.hyp hMod
  have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe ha hb
  have hU2 : ∀ u ∈ fsuU T V, u * u = 1 := fun u hu => by
    rw [← sq]
    exact F7.isElemAbelian_pow_eq_one hUe hu
  have hUN : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := hz_le_normalizer_U E.S.hyp hMod
  obtain ⟨-, hR1T⟩ := E.qh_le_r1
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hUK : fsuU T V ≤ oTwoUpper H := (E.u_le_l1 hF).trans hL1K
  have hDU : D ≤ Subgroup.centralizer (fsuU T V : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hDK d hd u (hUK hu)).symm
  obtain ⟨A, hA⟩ : ∃ A, Quasithin.conjSub g D = A := ⟨_, rfl⟩
  have hAR : A ≤ pCoreOf 2 (l1 T L V ⊔ T) := hA ▸ hg
  have hAH : A ≤ hz T V := (hAR.trans hR1T).trans E.t_le_hz
  have hA4 : Nat.card A = 4 := by
    rw [← hA, Quasithin.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hD4]
  have hTIA : ∀ u : G, ∀ a ∈ A, a ≠ 1 → a ∈ Quasithin.conjSub u A →
      Quasithin.conjSub u A = A := by
    intro u a ha ha1 hau
    by_contra hne
    have hne' : Quasithin.conjSub (g⁻¹ * u * g) D ≠ D := by
      intro h1
      apply hne
      rw [← hA, ← Quasithin.conjSub_mul, show u * g = g * (g⁻¹ * u * g) by group,
        Quasithin.conjSub_mul, h1]
    have hbot : D ⊓ Quasithin.conjSub (g⁻¹ * u * g) D = ⊥ := hTI _ hne'
    have hmem : g⁻¹ * a * g ∈ D ⊓ Quasithin.conjSub (g⁻¹ * u * g) D := by
      rw [← hA] at ha hau
      refine Subgroup.mem_inf.mpr ⟨Quasithin.mem_conjSub.mp ha, ?_⟩
      rw [Quasithin.mem_conjSub]
      have h2 := Quasithin.mem_conjSub.mp (Quasithin.mem_conjSub.mp hau)
      have e : (g⁻¹ * u * g)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * u * g) = g⁻¹ * (u⁻¹ * a * u) * g := by
        group
      rw [e]
      exact h2
    rw [hbot, Subgroup.mem_bot] at hmem
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  have hbang : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ fsuU T V, u * a = a * u → ∀ a' ∈ A,
      u * a' * u⁻¹ * a'⁻¹ ∈ A ⊓ fsuU T V := by
    intro a ha ha1 u hu hua a' ha'
    have hau : a ∈ Quasithin.conjSub u A := by
      rw [Quasithin.mem_conjSub]
      have e : u⁻¹ * a * u = a := by
        rw [mul_assoc, ← hua]
        group
      rw [e]
      exact ha
    have hAu := hTIA u a ha ha1 hau
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : u * a' * u⁻¹ ∈ A := by
        rw [← hAu]
        exact Quasithin.mul_mem_conjSub ha'
      exact mul_mem h1 (inv_mem ha')
    · have h1 : a' * u⁻¹ * a'⁻¹ ∈ fsuU T V :=
        (Subgroup.mem_normalizer_iff.mp (hUN (hAH ha')) _).mp (inv_mem hu)
      rw [show u * a' * u⁻¹ * a'⁻¹ = u * (a' * u⁻¹ * a'⁻¹) by group]
      exact mul_mem hu h1
  rw [hA]
  by_contra hAC
  by_cases hAU : A ⊓ fsuU T V = ⊥
  ·
    have hstar : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ fsuU T V, u * a = a * u → ∀ a' ∈ A,
        u * a' = a' * u := by
      intro a ha ha1 u hu hua a' ha'
      have h1 := hbang a ha ha1 u hu hua a' ha'
      rw [hAU, Subgroup.mem_bot] at h1
      calc u * a' = (u * a' * u⁻¹ * a'⁻¹) * a' * u := by group
        _ = a' * u := by rw [h1]; group
    have hfaith : ∀ a ∈ A, a ≠ 1 → ∃ u ∈ fsuU T V, u * a ≠ a * u := by
      intro a ha ha1
      by_contra hno
      push Not at hno
      exact hAC fun a' ha' => Subgroup.mem_centralizer_iff.mpr fun u hu =>
        hstar a ha ha1 u hu (hno u hu) a' ha'
    have hA2 : ∀ a ∈ A, a * a = 1 := by
      intro a ha
      by_contra hs1
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hs1 (mul_one 1)
      have ha4 : (a * a) * (a * a) = 1 := by
        have h1 : (⟨a, ha⟩ : ↥A) ^ Nat.card A = 1 := pow_card_eq_one'
        rw [hA4] at h1
        have h2 : a ^ 4 = 1 := by simpa using congrArg Subtype.val h1
        calc (a * a) * (a * a) = a ^ 2 * a ^ 2 := by rw [sq]
          _ = a ^ 4 := by rw [← pow_add]
          _ = 1 := h2
      have hsq : ∀ w ∈ fsuU T V, (a * a) * w = w * (a * a) → a * w = w * a := fun w hw hsw =>
        (hstar (a * a) (mul_mem ha ha) hs1 w hw hsw.symm a ha).symm
      obtain ⟨u, hu, hua⟩ := hfaith a ha ha1
      exact hua (comm_eq_of_sq_mem_centralizer hU2 (hUN (hAH ha)) ha4 hsq u hu).symm
    have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left (hA2 _ (mul_mem ha hb))).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by
          rw [inv_eq_of_mul_eq_one_left (hA2 b hb), inv_eq_of_mul_eq_one_left (hA2 a ha)]
    have hidxA := E.relIndex_inf_qh_le_two hAR hAc hA2
    have hcardAQ : 2 ≤ Nat.card ↥(A ⊓ pCoreOf 2 (hz T V)) := by
      have h1 := Subgroup.relIndex_mul_card (A ⊓ pCoreOf 2 (hz T V)) A
      rw [inf_eq_left.mpr (inf_le_left : A ⊓ pCoreOf 2 (hz T V) ≤ A), hA4] at h1
      by_contra hlt
      push Not at hlt
      have hpos : 0 < Nat.card ↥(A ⊓ pCoreOf 2 (hz T V)) := Nat.card_pos
      have h2 : Nat.card ↥(A ⊓ pCoreOf 2 (hz T V)) = 1 := by omega
      rw [h2, mul_one] at h1
      omega
    obtain ⟨b, hbAQ, hb1⟩ : ∃ b ∈ A ⊓ pCoreOf 2 (hz T V), b ≠ 1 := by
      by_contra hno
      push Not at hno
      have h0 : A ⊓ pCoreOf 2 (hz T V) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
      rw [h0, Subgroup.card_bot] at hcardAQ
      omega
    have hbA := (Subgroup.mem_inf.mp hbAQ).1
    have hbQ := (Subgroup.mem_inf.mp hbAQ).2
    have hbC : b ∉ Subgroup.centralizer (fsuU T V : Set G) := by
      intro hbC
      obtain ⟨u, hu, hub⟩ := hfaith b hbA hb1
      exact hub (Subgroup.mem_centralizer_iff.mp hbC u hu)
    have hidxb := E.relIndex_centralizer_qh hF hbQ hbC
    obtain ⟨a, ha, ha1, hab⟩ : ∃ a ∈ A, a ≠ 1 ∧ a ≠ b := by
      by_contra hno
      push Not at hno
      have h1 := card_le_of_forall_mem A {1, b} fun x hx => by
        by_cases hx1 : x = 1
        · simp [hx1]
        · simp [hno x hx hx1]
      rw [hA4] at h1
      have h2 := h1.trans Finset.card_le_two
      omega
    have hCeq : fsuU T V ⊓ Subgroup.centralizer ({b} : Set G) =
        fsuU T V ⊓ Subgroup.centralizer ({a} : Set G) := by
      ext u
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hu, hub⟩
        exact ⟨hu, hstar b hbA hb1 u hu hub a ha⟩
      · rintro ⟨hu, hua⟩
        exact ⟨hu, hstar a ha ha1 u hu hua b hbA⟩
    have haQ : a ∈ pCoreOf 2 (hz T V) := by
      by_contra haQ
      refine E.not_forall_comm_mem_v1 hF (hAH ha) haQ
        (W := fsuU T V ⊓ Subgroup.centralizer ({a} : Set G)) ?_ ?_
      · rw [← hCeq]
        exact hidxb.le
      · intro w hw
        have hwa : w * a = a * w :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2
        rw [show a * w * a⁻¹ * w⁻¹ = 1 by rw [← hwa]; group]
        exact (fsuV1 T V).one_mem
    have hba := E.inv_mul_mem_centralizer hF hbQ haQ hCeq
    have hba1 : b⁻¹ * a ≠ 1 := fun e => hab (inv_mul_eq_one.mp e).symm
    obtain ⟨u, hu, hu'⟩ := hfaith _ (mul_mem (inv_mem hbA) ha) hba1
    exact hu' (Subgroup.mem_centralizer_iff.mp hba u hu)
  ·
    obtain ⟨e, he, he1⟩ : ∃ e ∈ A ⊓ fsuU T V, e ≠ 1 := by
      by_contra hno
      push Not at hno
      exact hAU ((Subgroup.eq_bot_iff_forall _).mpr hno)
    have heA := (Subgroup.mem_inf.mp he).1
    have heU := (Subgroup.mem_inf.mp he).2
    have hUA : ∀ u ∈ fsuU T V, ∀ a' ∈ A, u * a' * u⁻¹ * a'⁻¹ ∈ A ⊓ fsuU T V := fun u hu =>
      hbang e heA he1 u hu (hUc u hu e heU)
    have hAUcard : Nat.card ↥(A ⊓ fsuU T V) ≤ 2 := by
      have hne : Nat.card ↥(A ⊓ fsuU T V) ≠ 4 := by
        intro h4
        have hAeq : A ⊓ fsuU T V = A :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hA4])
        refine hAC fun a' ha' => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
        have ha'U : a' ∈ A ⊓ fsuU T V := by
          rw [hAeq]
          exact ha'
        exact hUc u hu a' (Subgroup.mem_inf.mp ha'U).2
      have hdvd : Nat.card ↥(A ⊓ fsuU T V) ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hA4]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm3 with rfl | rfl | rfl
      · rw [hm']
        norm_num
      · rw [hm']
        norm_num
      · exact absurd (hm'.trans (by norm_num)) hne
    obtain ⟨a, haA, haC⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
    have haN : a ∈ Subgroup.normalizer (fsuU T V : Set G) := hUN (hAH haA)
    have hidx : (fsuU T V ⊓ Subgroup.centralizer ({a} : Set G)).relIndex (fsuU T V) ≤ 2 := by
      have hker : (commHom hUc haN).ker =
          (fsuU T V ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (fsuU T V) := by
        ext w
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
          Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro h1
          have h2 : a * (w : G) * a⁻¹ * (w : G)⁻¹ = 1 := congrArg Subtype.val h1
          refine ⟨w.2, ?_⟩
          calc (w : G) * a = (a * (w : G) * a⁻¹ * (w : G)⁻¹)⁻¹ * a * w := by group
            _ = a * w := by rw [h2]; group
        · rintro ⟨-, h2⟩
          apply Subtype.ext
          show a * (w : G) * a⁻¹ * (w : G)⁻¹ = 1
          rw [← h2]
          group
      have hrange : Nat.card (commHom hUc haN).range ≤ 2 := by
        refine le_trans ?_ hAUcard
        rw [← Subgroup.card_map_of_injective (fsuU T V).subtype_injective]
        refine Subgroup.card_le_of_le ?_
        rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
        have h1 := hUA w w.2 a haA
        have e : (fsuU T V).subtype (commHom hUc haN w) = ((w : G) * a * (w : G)⁻¹ * a⁻¹)⁻¹ := by
          show a * (w : G) * a⁻¹ * (w : G)⁻¹ = _
          group
        rw [e]
        exact inv_mem h1
      rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
      exact hrange
    have haQ : a ∈ pCoreOf 2 (hz T V) := by
      by_contra haQ
      refine E.not_forall_comm_mem_v1 hF (hAH haA) haQ
        (W := fsuU T V ⊓ Subgroup.centralizer ({a} : Set G)) hidx ?_
      intro w hw
      have hwa : w * a = a * w :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2
      rw [show a * w * a⁻¹ * w⁻¹ = 1 by rw [← hwa]; group]
      exact (fsuV1 T V).one_mem
    obtain ⟨u, hu, hua⟩ : ∃ u ∈ fsuU T V, u * a ≠ a * u := by
      by_contra hno
      push Not at hno
      exact haC (Subgroup.mem_centralizer_iff.mpr hno)
    have hcV1 : a * u * a⁻¹ * u⁻¹ ∈ fsuV1 T V :=
      hF.toHypF91.commutator_mem_V₁ haQ (E.fsuU_eq ▸ hu)
    have hcA : a * u * a⁻¹ * u⁻¹ ∈ A := by
      have h1 := (Subgroup.mem_inf.mp (hUA u hu a haA)).1
      rw [show a * u * a⁻¹ * u⁻¹ = (u * a * u⁻¹ * a⁻¹)⁻¹ by group]
      exact inv_mem h1
    have hc1 : a * u * a⁻¹ * u⁻¹ ≠ 1 := by
      intro h1
      apply hua
      calc u * a = (a * u * a⁻¹ * u⁻¹)⁻¹ * a * u := by group
        _ = a * u := by rw [h1]; group
    have hAD : A = D := by
      by_contra hne
      have hne' : Quasithin.conjSub g D ≠ D := by
        rw [hA]
        exact hne
      have hbot : D ⊓ Quasithin.conjSub g D = ⊥ := hTI g hne'
      have hmem : a * u * a⁻¹ * u⁻¹ ∈ D ⊓ Quasithin.conjSub g D := by
        rw [hA]
        exact Subgroup.mem_inf.mpr ⟨hV1D hcV1, hcA⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hc1 hmem
    apply hAC
    rw [hAD]
    exact hDU

theorem false_of_ti {D : Subgroup G} (hTI : fusionIsTI D) (hDK : D ≤ oTwoUpper H)
    (hDc : ∀ d ∈ D, ∀ k ∈ oTwoUpper H, d * k = k * d) (hD4 : Nat.card D = 4)
    (hV1D : fsuV1 T V ≤ D) (hDn : H ≤ Subgroup.normalizer (D : Set G)) : False := by
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  have hD1 : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hD4
    omega
  have hD2 : IsPGroup 2 ↥D := IsPGroup.of_card (n := 2) (by rw [hD4]; norm_num)
  refine E.false_of_conj_le_centralizer hF hD1 hD2 (hDK.trans E.k_le_hz) ?_
    fun g hg => E.conj_le_centralizer_of_ti hF hTI hD4 hV1D hDc hg
  rw [← hH]
  exact hDn

end Ctx7153

end CFSG.Quasithin.H13.L32A
