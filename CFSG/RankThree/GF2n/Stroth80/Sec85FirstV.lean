module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Canon
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootMain
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal
public import CFSG.RankThree.GF2n.Stroth80.Sec8SectionOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel
public import CFSG.RankThree.GF2n.Stroth80.Sec8FixedPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GroupTheory.SteinbergBY (isPGroup_inSubgroup_pCore)
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_irred_V (hc : Ctx M Q Z B) {t : G} {m : ℕ} (hmSp : SpMNat hc t m) :
    ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ U = U) → U = Z ∨ U = Vt M (LB M Q B) B Z t := by
  obtain ⟨K, fK, finK, hK, hrep⟩ := hmSp
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  intro U hZU hUV hinv
  exact NaturalRep.eq_or_eq_of_invariant natIrred_statedSp addCommutantScalar_statedSp hrep hZU
    hUV (fun r hr u hu => conj_mem_of_conjSubgroup_eq (hinv r hr) hu)

theorem sec8_comm_V_mem_Z (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {m : ℕ}
    (hmSp : SpMNat hc t m) {x : G} (hxM : x ∈ M)
    (hxV : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)) {k : ℕ} (hxk : x ^ (2 ^ k) = 1)
    (hxR : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * x * ρ⁻¹ * x⁻¹ ∈ hc.CN t) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hsec : SecHyp (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z :=
    ⟨sec39_Z_le_Vt, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V (hVQ hx) (hVQ hy),
      fun x hx => hc.hyp.toHyp79.sq_mem_V (hVQ hx),
      fun r hr y hy => (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) y).mp hy,
      fun r hr y hy => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hRM hr)) y).mp hy⟩
  exact sec8_isol hsec (fun y hy => (Subgroup.mem_normalizer_iff.mp hxV y).mp hy)
    (fun y hy => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) y).mp hy) hxR
    (fun n hn y hy => (Ctx.mem_CN.mp hn).2 y hy) hxk (sec8_irred_V hc hmSp)


theorem sec8_comm_V1_mem_Z (h310chi : Stroth310ChiStatement) (h53 : Stroth53Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {m : ℕ}
    (hmSp : SpMNat hc t m) (hm2 : 2 ≤ m) {x : G} (hxH : x ∈ H0 M Z)
    (hxV₁ : x ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G)) {k : ℕ}
    (hxk : x ^ (2 ^ k) = 1)
    (hxR : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * x * ρ⁻¹ * x⁻¹ ∈ hc.CN t)
    (hVfix : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) :
    ∀ v ∈ Sec8V1 M Q Z B t r, ⁅x, v⁆ ∈ Z := by
  classical
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hxM : x ∈ M := hxH.1
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K, iF, iFin, hchar, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI : CharP K 2 := hchar
  haveI hEfin : Module.Finite K M₀.E := M₀.fin
  haveI hEfinite : Finite M₀.E := Module.finite_of_finite K
  obtain ⟨A, A₀, hAmem, hA₀mem, hA₀A, hdim⟩ := sec8_exists_codim_one h310chi h53.1 hc hs hr hD
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  set xH : ↥(H0 M Z) := ⟨x, hxH⟩ with hxHdef
  set T : M₀.E ≃ₗ[K] M₀.E := φ xH with hT
  have hTπ : ∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y) := fun y hy => hφπ xH y hy
  set ν : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - 1 with hν
  have hνapp : ∀ e, ν e = T e - e := fun e => by simp [hν]
  have hTpow : (T : M₀.E →ₗ[K] M₀.E) ^ (2 ^ k) = 1 := by
    have h1 : T ^ (2 ^ k) = 1 := by
      rw [hT, ← map_pow]
      have : xH ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk)
      rw [this, map_one]
    refine LinearMap.ext fun e => ?_
    have h2 := LinearEquiv.congr_fun h1 e
    simpa [LinearEquiv.coe_pow, Module.End.pow_apply] using h2
  have hνnil : ν ^ (2 ^ k) = 0 := linearMap_sub_one_pow_two_pow _ hTpow
  have hAT : ∀ a ∈ A, T a ∈ A := by
    intro a ha
    obtain ⟨u, hu, huQ, rfl⟩ := (hAmem a).mp ha
    rw [← hTπ u huQ]
    exact (hAmem _).mpr (M₀.pi_mem_img ((Subgroup.mem_normalizer_iff.mp hxV₁ u).mp hu)
      (hQn x hxM u huQ))
  have hνA : ∀ a ∈ A, ν a ∈ A := fun a ha => by
    rw [hνapp]
    exact A.sub_mem (hAT a ha) ha
  have hν0 : ∀ a ∈ A₀, ν a = 0 := by
    intro a ha
    obtain ⟨v, hv, hvQ, rfl⟩ := (hA₀mem a).mp ha
    have hcz : ⁅x, v⁆ ∈ Z := hVfix v hv
    have h0 : M₀.π ⁅x, v⁆ = 0 := (M₀.π_ker _ (hZQ hcz)).mpr hcz
    have hπ := sec8_pi_comm M₀ hvQ (hQn x hxM v hvQ) (hTπ v hvQ)
    rw [hνapp, ← hπ]
    exact h0
  obtain ⟨a₀, ha₀, hspan⟩ := nilp_hyperplane ν hνnil A₀ A hA₀A hdim hνA hν0
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hRinv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs r hr ρ hρ
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have h53d := h53.2.2.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hρA : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t) (b : M₀.E), b ∈ A →
      φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ b ∈ A := by
    intro ρ hρ b hb
    obtain ⟨u, hu, huQ, rfl⟩ := (hAmem b).mp hb
    rw [← hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u huQ]
    exact (hAmem _).mpr (M₀.pi_mem_img (conj_mem_of_conjSubgroup_eq (hRinv ρ hρ).1 hu)
      (hQn ρ (hRM hρ) u huQ))
  have hcomm : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t) (a : M₀.E), a ∈ A →
      φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ (ν a) = ν (φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ a) := by
    intro ρ hρ a ha
    have hcN := hxR ρ hρ
    set ρH : ↥(H0 M Z) := ⟨ρ, hc.Rt_le_H0 t hρ⟩ with hρH
    set cH : ↥(H0 M Z) := ⟨ρ * x * ρ⁻¹ * x⁻¹, hc.Rt_le_H0 t (hNR hcN)⟩ with hcHdef
    have hrel : ρH * xH = cH * xH * ρH := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hcHdef, hρH, hxHdef]
      group
    have hfixA : ∀ b ∈ A, φ cH b = b := by
      intro b hb
      obtain ⟨u, hu, huQ, rfl⟩ := (hAmem b).mp hb
      have hcu : ⁅ρ * x * ρ⁻¹ * x⁻¹, u⁆ ∈ Z := h53d.1 _ hcN u hu
      have hcuQ : ⁅ρ * x * ρ⁻¹ * x⁻¹, u⁆ ∈ Q := hZQ hcu
      rw [← hφπ cH u huQ]
      have e : (ρ * x * ρ⁻¹ * x⁻¹) * u * (ρ * x * ρ⁻¹ * x⁻¹)⁻¹ =
          ⁅ρ * x * ρ⁻¹ * x⁻¹, u⁆ * u := by
        simp only [commutatorElement_def]
        group
      show M₀.π ((ρ * x * ρ⁻¹ * x⁻¹) * u * (ρ * x * ρ⁻¹ * x⁻¹)⁻¹) = M₀.π u
      rw [e, M₀.π_mul _ hcuQ _ huQ, (M₀.π_ker _ hcuQ).mpr hcu, zero_add]
    have hTρ : φ ρH (T a) = T (φ ρH a) := by
      have h1 : φ (ρH * xH) a = φ (cH * xH * ρH) a := by rw [hrel]
      rw [map_mul, map_mul, map_mul] at h1
      simp only [LinearEquiv.mul_apply] at h1
      rw [hfixA _ (hAT _ (hρA ρ hρ a ha))] at h1
      exact h1
    rw [hνapp, hνapp, map_sub, hTρ]
  set Y : Submodule K M₀.E := A.map ν with hY
  have hYA₀ : ∀ y ∈ Y, y ∈ A₀ := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨r', hr'⟩ := hspan a ha
    rw [hr']
    exact A₀.smul_mem _ ha₀
  let S : Subgroup G := M₀.lift Y.toAddSubgroup
  have hZS : Z ≤ S := fun z hz =>
    ⟨hZQ hz, by rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact Y.zero_mem⟩
  have hSV : S ≤ Vt M (LB M Q B) B Z t := by
    intro u hu
    have h1 : M₀.π u ∈ M₀.img (Vt M (LB M Q B) B Z t) := (hA₀mem _).mp (hYA₀ _ hu.2)
    exact (M₀.mem_img_iff hZV hu.1).mp h1
  have hSinv : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ S = S := by
    intro ρ hρ
    refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun u hu => ?_)
    refine ⟨hQn ρ (hRM hρ) u hu.1, ?_⟩
    obtain ⟨a, ha, hau⟩ := hu.2
    show M₀.π (ρ * u * ρ⁻¹) ∈ Y
    rw [hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u hu.1, ← hau, hcomm ρ hρ a ha]
    exact ⟨_, hρA ρ hρ a ha, rfl⟩
  rcases sec8_irred_V hc hmSp S hZS hSV hSinv with hS | hS
  ·
    intro v hv
    have hvQ : v ∈ Q := sec8_V1_le_Q hc t r hv
    have hπv : M₀.π v ∈ A := (hAmem _).mpr (M₀.pi_mem_img hv hvQ)
    obtain ⟨u, huQ, hu⟩ := M₀.π_surj (ν (M₀.π v))
    have huS : u ∈ S := ⟨huQ, by rw [hu]; exact ⟨_, hπv, rfl⟩⟩
    rw [hS] at huS
    have h0 : ν (M₀.π v) = 0 := by rw [← hu]; exact (M₀.π_ker u huQ).mpr huS
    have hcQ : ⁅x, v⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (hQn x hxM v hvQ) (Q.inv_mem hvQ)
    have hπ := sec8_pi_comm M₀ hvQ (hQn x hxM v hvQ) (hTπ v hvQ)
    exact (M₀.π_ker _ hcQ).mp (by rw [hπ, ← hνapp, h0])
  ·
    exfalso
    have hA₀Y : ∀ e ∈ A₀, e ∈ Y := by
      intro e he
      obtain ⟨v, hvV, hvQ, rfl⟩ := (hA₀mem e).mp he
      have hvS : v ∈ S := hS ▸ hvV
      obtain ⟨a, ha, hav⟩ := hvS.2
      exact ⟨a, ha, hav⟩
    have hsub : A₀ ≤ Submodule.span K {a₀} := by
      intro e he
      obtain ⟨a, ha, hae⟩ := hA₀Y e he
      obtain ⟨r', hr'⟩ := hspan a ha
      rw [← hae, hr']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a₀)
    have hfr : Module.finrank K A₀ ≤ 1 := by
      refine (Submodule.finrank_mono hsub).trans ?_
      by_cases ha : a₀ = 0
      · rw [ha, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        omega
      · rw [finrank_span_singleton ha]
    have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
    have hcV : Nat.card ↥(Vt M (LB M Q B) B Z t) =
        Nat.card Z * Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) := M₀.card_eq hVQ hZV
    have hcard : Nat.card ↥A₀ = Nat.card Z ^ (2 * m) := by
      have h1 : Nat.card ↥A₀ = Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) :=
        Nat.card_congr (Equiv.subtypeEquivRight hA₀mem)
      have h2 : Nat.card Z ^ (2 * m + 1) =
          Nat.card Z * Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) := by
        rw [← hmSp.card_V]
        exact hcV
      rw [h1]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
      rw [← h2]
      ring
    have hfin : Module.finrank K A₀ = 2 * m := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥A₀), hD.card] at hcard
      exact Nat.pow_right_injective hq2 hcard
    omega


theorem sec8_comm_W1_mem_V1 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h53 : Stroth53Statement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t)
    (hr : Sec7A hc t r) (hC : Conc83 hc n t) {x : G} (hxM : x ∈ M)
    (hxV₁ : x ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G)) {k : ℕ}
    (hxk : x ^ (2 ^ k) = 1)
    (hxR : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * x * ρ⁻¹ * x⁻¹ ∈ hc.CN t) :
    ∀ w ∈ Sec8W1 M Q Z B t r, ⁅x, w⁆ ∈ Sec8V1 M Q Z B t r := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨m, hn11, hmSp⟩ : ∃ m : ℕ, (n = 11 ∧ m = 3 ∨ n = 17 ∧ m = 4) ∧ SpMNat hc t m := by
    rcases hC with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨3, Or.inl ⟨h1, rfl⟩, h2⟩
    · exact ⟨4, Or.inr ⟨h1, rfl⟩, h2⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, -⟩ := sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs r hr ρ hρ
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8W1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).2 hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8V1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).1 hy
  have h53b := h53.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53c := h53.2.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hsec : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    SecHyp.of_isOppDecomp h53c hP hI
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem ht hrR
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  obtain ⟨a, han, -, hWc⟩ := sec83_count_A h53 sec8InvStatement_holds hs5 hr hpts
  have ha1 : a = 1 := by
    rcases hn11 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h2 <;> subst h1 <;> omega
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hpos : 0 < Nat.card ↥(Sec8V1 M Q Z B t r) := Nat.card_pos
  have hWV : Nat.card ↥(Sec8W1 M Q Z B t r) =
      Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 ^ m) := by
    rw [hWc, ha1, one_mul]
  have hirr : ∀ U : Subgroup G, Sec8V1 M Q Z B t r ≤ U → U ≤ Sec8W1 M Q Z B t r →
      (∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ U = U) →
      U = Sec8V1 M Q Z B t r ∨ U = Sec8W1 M Q Z B t r := by
    intro U hIU hUP hUinv
    obtain ⟨-, b, hb⟩ := sec8_invariant_section (R := Rt M (LB M Q B) t) (N := hc.CN t)
      (P := Sec8W1 M Q Z B t r) (I := Sec8V1 M Q Z B t r) (L₁ := LB M Q B)
      (L₂ := LB M Q (conjSubgroup r B))
      (A₁ := (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
      (A₂ := (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) (U := U) φ
      hpts.range (by omega) hpts.ker hP hI h53b.2 h53c hLR hLCR hpts.uu' hpts.u_ne_zero hpts.hL
      hL2 (fun y hy => hQN (hc.sq_mem_Q_of_mem_LB hy)) hrR (hc.LB_conj hrM).symm hIU hUP hUinv
    rw [hpts.card] at hb
    have hle : Nat.card ↥U ≤ Nat.card ↥(Sec8W1 M Q Z B t r) := Subgroup.card_le_of_le hUP
    rw [hb, hWV] at hle
    have h1 : Nat.card Z ^ (2 ^ m * b) ≤ Nat.card Z ^ (2 ^ m) :=
      Nat.le_of_mul_le_mul_left hle hpos
    have h2 : 2 ^ m * b ≤ 2 ^ m := (Nat.pow_le_pow_iff_right hq2).mp h1
    have hb1 : b ≤ 1 := by
      by_contra hb2
      have : 2 ^ m * 2 ≤ 2 ^ m * b := Nat.mul_le_mul_left _ (by omega)
      have : 0 < 2 ^ m := by positivity
      omega
    interval_cases b
    · left
      exact (Subgroup.eq_of_le_of_card_ge hIU (by rw [hb]; simp)).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hUP (by rw [hb, hWV]; simp)
  exact sec8_isol hsec (fun y hy => (Subgroup.mem_normalizer_iff.mp
      (sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 hxM) (hxV₁)) y).mp hy)
    (fun y hy => (Subgroup.mem_normalizer_iff.mp hxV₁ y).mp hy) hxR h53b.2 hxk hirr


theorem step85FirstV_of_83 (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) (hzt : Sec8ZtStatement)
    (hA : Sec8AExistsStatement) (h83 : Stroth83Statement) : Step85FirstVStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 x hx hxR
  classical
  have hRoot := stroth310Root_of_34 h34
  have hxK : x ∈ NormH0 M Z Z0 := by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  obtain ⟨k, hxk⟩ : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_inSubgroup_pCore 2 (NormH0 M Z Z0) ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hxH : x ∈ H0 M Z := hxK.1
  have hxM : x ∈ M := hxH.1
  obtain ⟨-, hxVt⟩ := sec8_normalizes_of_zt hzt h51 hA hc hs hZ0 hxK
  have hxV : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxVt
  have hxV₁ : x ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sec8Canon_of h34 hRoot G M Q Z B hc n t hs r hr x hxM hxV
  have hxR' : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * x * ρ⁻¹ * x⁻¹ ∈ hc.CN t := fun ρ hρ => by
    have h1 := (hc.CN t).inv_mem (hxR ρ hρ)
    rwa [commutatorElement_inv, commutatorElement_def] at h1
  have hC := h83 G M Q Z B hc n t hs.toSec5 hs.sp
  have hmSp : ∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m := by
    rcases hC with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
    · exact ⟨3, by norm_num, h2⟩
    · exact ⟨4, by norm_num, h2⟩
  obtain ⟨m, hm2, hmSp⟩ := hmSp
  have hVfix := sec8_comm_V_mem_Z hc hs.toSec5.mem hmSp hxM hxV hxk hxR'
  exact ⟨sec8_comm_V1_mem_Z h310chi h53 hc hs hr hmSp hm2 hxH hxV₁ hxk hxR' hVfix,
    sec8_comm_W1_mem_V1 h34 hRoot h53 hc hs hr hC hxM hxV₁ hxk hxR'⟩

end CFSG.RankThree.GF2n.Stroth80
