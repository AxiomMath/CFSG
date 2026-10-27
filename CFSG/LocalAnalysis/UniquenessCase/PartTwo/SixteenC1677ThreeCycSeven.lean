module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycConc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycSevenBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycSevenCent
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

private lemma s168e3_cyc_mem_stabSub_of_map_eq {U : Subgroup W} {g : MulAut W}
    (h : U.map g.toMonoidHom = U) : g ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    exact (Subgroup.mem_map_iff_mem (f := g.toMonoidHom) g.injective).mp (h.symm ▸ hu)
  · intro hu
    exact h ▸ (Subgroup.mem_map_iff_mem (f := g.toMonoidHom) g.injective).mpr hu

private lemma s168e3_cyc7_x_invariant_map {A L : Subgroup (MulAut W)} {x g : MulAut W}
    {U : Subgroup W} (hLx : L = Subgroup.zpowers x)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hgA : g ∈ A) (hxU : x ∈ stabSub U) :
    ∀ u ∈ U.map g.toMonoidHom, x u ∈ U.map g.toMonoidHom := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  have hmem : g⁻¹ * x * g ∈ L := by
    have hxL : x ∈ L := by rw [hLx]; exact Subgroup.mem_zpowers x
    have hmem' : (MulAut.conj g⁻¹) x ∈ L.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hxL
    rw [hLn g⁻¹ (A.inv_mem hgA)] at hmem'
    simpa [MulAut.conj_apply] using hmem'
  have hmem_z : g⁻¹ * x * g ∈ Subgroup.zpowers x := by rwa [hLx] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem_z
  have hxk : x ^ k ∈ stabSub U :=
    Subgroup.zpowers_le.mpr hxU ((Subgroup.zpowers x).zpow_mem (Subgroup.mem_zpowers x) k)
  have hxgy : x ((MulEquiv.toMonoidHom g) v) = g ((g⁻¹ * x * g) v) := by
    simp [MulAut.mul_apply]
  rw [hxgy, ← hk]
  exact Subgroup.mem_map_of_mem g.toMonoidHom ((mem_stabSub.mp hxk v).2 hv)

private lemma s168e3_cyc7_invariant_eq (hcard : Nat.card W = 2 ^ 6) {W₁ W₂ U : Subgroup W}
    {x : MulAut W}
    (hinvar : ∀ U : Subgroup W, (∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = W₁ ∨ U = W₂ ∨ U = ⊤)
    (hU : ∀ u ∈ U, x u ∈ U) (hUcard : Nat.card ↥U = 8) : U = W₁ ∨ U = W₂ := by
  rcases hinvar U hU with h | h | h | h
  · rw [h, Subgroup.card_bot] at hUcard
    norm_num at hUcard
  · exact Or.inl h
  · exact Or.inr h
  · rw [h, Subgroup.card_top, hcard] at hUcard
    norm_num at hUcard

private lemma s168e3_cyc_not_sq_dvd_294 {r : ℕ} (hr : r.Prime) (hr7 : r ≠ 7) :
    ¬ r ^ 2 ∣ 294 := by
  intro h
  have hr294 : r ∣ 294 := (dvd_mul_right r r).trans (by rwa [pow_two] at h)
  have hcases : r = 2 ∨ r = 3 ∨ r = 7 := by
    have h294 : (294 : ℕ) = 2 * (3 * 7 ^ 2) := by norm_num
    rw [h294] at hr294
    rcases (hr.dvd_mul).mp hr294 with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
      · exact absurd h1 hr.ne_one
      · exact Or.inl h2
    · rcases (hr.dvd_mul).mp h with h | h
      · rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h2
        · exact absurd h1 hr.ne_one
        · exact Or.inr (Or.inl h2)
      · rcases (Nat.dvd_prime Nat.prime_seven).mp (hr.dvd_of_dvd_pow h) with h1 | h2
        · exact absurd h1 hr.ne_one
        · exact Or.inr (Or.inr h2)
  rcases hcases with rfl | rfl | rfl
  · norm_num at h
  · norm_num at h
  · exact absurd rfl hr7

theorem s168e3_cyc7_main [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {A L : Subgroup (MulAut W)} {t x : MulAut W} (hLx : L = Subgroup.zpowers x)
    (hxo : orderOf x = 7) (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hfpf : ∀ w : W, x w = w → w = 1) (ht : t ∈ A) (hinv : t * x * t⁻¹ = x⁻¹) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqm : 2 ≤ CFSG.Open.pRank q A) :
    ∃ K : Subgroup (MulAut W), Conc4_136W A t K ∧ IsCyclicOrd ↥K 7 ∧ rk ↥(commSub ⊤ K) = 3 ∧
      Set.ncard {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} = 2 ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 7 → CFSG.Open.pRank r A < 2 := by
  classical
  have hx7 : x ^ 7 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxo] at h
  have hLcard : Nat.card ↥L = 7 := by rw [hLx, Nat.card_zpowers, hxo]
  have hxL : x ∈ L := by rw [hLx]; exact Subgroup.mem_zpowers x
  obtain ⟨W₁, W₂, hW₁card, hW₂card, hinf, hsup, ht₁, ht₂, hinvar, hcomm⟩ :=
    s168e3_cyc7_blocks hW hcard hx7 hfpf hinv
  have hxmap₁ : W₁.map x.toMonoidHom = W₁ := (hcomm x rfl).1
  have hxmap₂ : W₂.map x.toMonoidHom = W₂ := (hcomm x rfl).2
  have hx₁ : x ∈ stabSub W₁ := s168e3_cyc_mem_stabSub_of_map_eq hxmap₁
  have hx₂ : x ∈ stabSub W₂ := s168e3_cyc_mem_stabSub_of_map_eq hxmap₂
  have hW₁neW₂ : W₁ ≠ W₂ := by
    intro h
    have hbot : W₁ = ⊥ := by
      rw [← h, inf_idem] at hinf
      exact hinf
    rw [hbot, Subgroup.card_bot] at hW₁card
    norm_num at hW₁card
  let C : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (L : Set (MulAut W))
  have hCx : ∀ c ∈ C, c * x = x * c := by
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x hxL).symm
  have hCstab₁ : C ≤ stabSub W₁ := by
    intro c hc
    exact s168e3_cyc_mem_stabSub_of_map_eq (hcomm c (hCx c hc)).1
  have hCstab₂ : C ≤ stabSub W₂ := by
    intro c hc
    exact s168e3_cyc_mem_stabSub_of_map_eq (hcomm c (hCx c hc)).2
  have hn₁ : ∃ y ∈ W₁, x y ≠ y := by
    by_contra h
    push Not at h
    have hbot : W₁ = ⊥ :=
      (Subgroup.eq_bot_iff_forall W₁).mpr fun y hy => hfpf y (h y hy)
    rw [hbot, Subgroup.card_bot] at hW₁card
    norm_num at hW₁card
  have hn₂ : ∃ y ∈ W₂, x y ≠ y := by
    by_contra h
    push Not at h
    have hbot : W₂ = ⊥ :=
      (Subgroup.eq_bot_iff_forall W₂).mpr fun y hy => hfpf y (h y hy)
    rw [hbot, Subgroup.card_bot] at hW₂card
    norm_num at hW₂card
  have hdiv :=
    s168e3_cyc7_card_dvd hW hW₁card hW₂card hsup hx₁ hx₂ hx7 hn₁ hn₂ hCstab₁ hCstab₂ hCx
  have hcardC_eq :
      Nat.card ↥(autSub C W₂) * Nat.card ↥(C ⊓ centSub W₂) = Nat.card ↥C :=
    card_autSub_mul (A := C) (U := W₂) hCstab₂
  have hC_dvd : Nat.card ↥C ∣ 49 := by
    have h := mul_dvd_mul hdiv.1 hdiv.2
    rw [← hcardC_eq]
    norm_num at h ⊢
    exact h
  have hA_dvd : Nat.card ↥A ∣ 6 * Nat.card ↥C := by
    have h := s168e3_cyc_card_dvd (p := 7) (by norm_num) hLcard hLn
    norm_num at h
    exact h
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt A
  have hq_dvd : q ^ 2 ∣ Nat.card ↥A := by
    have h1 : q ^ 2 ∣ Nat.card ↥E := by rw [hEcard]; exact pow_dvd_pow q hqm
    exact h1.trans (Subgroup.card_dvd_of_le hEA)
  have hA_dvd294 : Nat.card ↥A ∣ 294 := by
    have h := hA_dvd.trans (mul_dvd_mul_left 6 hC_dvd)
    norm_num at h
    exact h
  have hq294 : q ^ 2 ∣ 294 := hq_dvd.trans hA_dvd294
  have hq7 : q = 7 := by
    by_contra hq7
    exact s168e3_cyc_not_sq_dvd_294 hq hq7 hq294
  have h49_dvd_C : 49 ∣ Nat.card ↥C := by
    have h : 7 ^ 2 ∣ 6 * Nat.card ↥C := by
      rw [← hq7]
      exact hq_dvd.trans hA_dvd
    have h' : (49 : ℕ) ∣ 6 * Nat.card ↥C := by simpa using h
    exact (show Nat.Coprime 49 6 by norm_num).dvd_of_dvd_mul_left h'
  have hCcard : Nat.card ↥C = 49 := (Nat.dvd_antisymm h49_dvd_C hC_dvd).symm
  let B : Subgroup (MulAut W) :=
    A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓ stabSub W₁ ⊓ stabSub W₂
  let K : Subgroup (MulAut W) := B ⊓ centSub W₂
  have hB₁ : B ≤ stabSub W₁ := fun b hb => (Subgroup.mem_inf.mp hb).1.2
  have hB₂ : B ≤ stabSub W₂ := fun b hb => (Subgroup.mem_inf.mp hb).2
  have hBC : B = C := by
    rw [show B = A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓ stabSub W₁ ⊓ stabSub W₂
      from rfl]
    rw [inf_eq_left.mpr hCstab₁, inf_eq_left.mpr hCstab₂]
  have hBcard : Nat.card ↥B = 49 := by rw [hBC, hCcard]
  have hBp : IsPGroup 7 ↥B := IsPGroup.of_card (n := 2) (by rw [hBcard]; norm_num)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    intro a ha b hb
    simpa using CFSG.Quasithin.commutative_of_card_le_prime_sq hBp
      (by rw [hBcard]; norm_num) ⟨a, ha⟩ ⟨b, hb⟩
  have hKcard : Nat.card ↥K = 7 := by
    have hprod : Nat.card ↥(autSub C W₂) * Nat.card ↥(C ⊓ centSub W₂) = 49 := by
      rw [hcardC_eq, hCcard]
    have hb : Nat.card ↥(C ⊓ centSub W₂) = 7 := by
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdiv.2 with h1 | h7
      · exfalso
        have h49 : Nat.card ↥(autSub C W₂) = 49 := by
          rw [h1, mul_one] at hprod
          exact hprod
        have hle := Nat.le_of_dvd (by norm_num) hdiv.1
        omega
      · exact h7
    rw [show K = B ⊓ centSub W₂ from rfl, hBC]
    exact hb
  have hKc : IsCyclicOrd ↥K 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact ⟨isCyclic_of_prime_card hKcard, hKcard⟩
  have hKB : K ≤ B := fun k hk => (Subgroup.mem_inf.mp hk).1
  have hKcent : K ≤ centSub W₂ := fun k hk => (Subgroup.mem_inf.mp hk).2
  have hKbot : K ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥K = 1 := by rw [h, Subgroup.card_bot]
    omega
  have hne_bot : commSub ⊤ K ≠ ⊥ := by
    intro h
    apply hKbot
    rw [Subgroup.eq_bot_iff_forall K]
    intro k hk
    ext w
    have hmem : k w * w⁻¹ ∈ commSub ⊤ K :=
      Subgroup.subset_closure ⟨k, hk, w, Subgroup.mem_top w, rfl⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hle : commSub ⊤ K ≤ W₁ := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, w, -, rfl⟩
    have hk₁ : k ∈ stabSub W₁ := hB₁ (hKB hk)
    have hk₂ : k ∈ centSub W₂ := hKcent hk
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ :=
      Subgroup.mem_sup.mp (by rw [hsup]; exact Subgroup.mem_top w)
    have hmul : k (a₁ * a₂) * (a₁ * a₂)⁻¹ = k a₁ * a₁⁻¹ := by
      rw [map_mul, mem_centSub.mp hk₂ a₂ ha₂]
      group
    rw [hmul]
    exact W₁.mul_mem ((mem_stabSub.mp hk₁ a₁).2 ha₁) (W₁.inv_mem ha₁)
  have hfixx : ∀ k ∈ K, MulAut.conj x k = k := by
    intro k hk
    have hkC : k ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      have hkB : k ∈ B := hKB hk
      have hkB' : k ∈ (A ⊓ Subgroup.centralizer (L : Set (MulAut W))) ⊓ stabSub W₁ :=
        (Subgroup.mem_inf.mp hkB).1
      exact (Subgroup.mem_inf.mp hkB').1.2
    have hxk : x * k = k * x := Subgroup.mem_centralizer_iff.mp hkC x hxL
    rw [MulAut.conj_apply, hxk]
    group
  have hKx : K.map (MulAut.conj x).toMonoidHom = K := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      show MulAut.conj x k ∈ K
      rw [hfixx k hk]
      exact hk
    · intro y hy
      exact Subgroup.mem_map.mpr ⟨y, hy, hfixx y hy⟩
  have hxinv : ∀ u ∈ commSub ⊤ K, x u ∈ commSub ⊤ K := by
    intro u hu
    have hmap := CFSG.Quasithin.Asc81c.commSub_map_conj K x
    rw [hKx] at hmap
    rw [hmap]
    exact Subgroup.mem_map_of_mem x.toMonoidHom hu
  have hKW : commSub ⊤ K = W₁ := by
    rcases hinvar (commSub ⊤ K) hxinv with hb | hW₁eq | hW₂eq | htop
    · exact absurd hb hne_bot
    · exact hW₁eq
    · exfalso
      have hle₂ : W₂ ≤ W₁ := by rw [← hW₂eq]; exact hle
      have hbot : W₂ = ⊥ := by rw [← inf_eq_left.mpr hle₂, inf_comm, hinf]
      rw [hbot, Subgroup.card_bot] at hW₂card
      norm_num at hW₂card
    · exfalso
      have htopW₁ : W₁ = ⊤ := top_le_iff.mp (by rw [← htop]; exact hle)
      rw [htopW₁, Subgroup.card_top, hcard] at hW₁card
      norm_num at hW₁card
  have hrkW₁ : rk ↥W₁ = 3 := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [CFSG.Quasithin.rk, hW₁card, h8, padicValNat.prime_pow]
  have hperm : ∀ g ∈ A, (W₁.map g.toMonoidHom = W₁ ∧ W₂.map g.toMonoidHom = W₂) ∨
      (W₁.map g.toMonoidHom = W₂ ∧ W₂.map g.toMonoidHom = W₁) := by
    intro g hgA
    have hmapg₁ : W₁.map g.toMonoidHom = W₁ ∨ W₁.map g.toMonoidHom = W₂ :=
      s168e3_cyc7_invariant_eq (W₁ := W₁) (W₂ := W₂) hcard hinvar
        (s168e3_cyc7_x_invariant_map hLx hLn hgA hx₁)
        (by rw [Subgroup.card_map_of_injective g.injective, hW₁card])
    have hmapg₂ : W₂.map g.toMonoidHom = W₂ ∨ W₂.map g.toMonoidHom = W₁ :=
      (s168e3_cyc7_invariant_eq (W₁ := W₁) (W₂ := W₂) hcard hinvar
        (s168e3_cyc7_x_invariant_map hLx hLn hgA hx₂)
        (by rw [Subgroup.card_map_of_injective g.injective, hW₂card])).symm
    rcases hmapg₁ with h1 | h1 <;> rcases hmapg₂ with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exfalso
      exact hW₁neW₂ (Subgroup.map_injective g.injective (h1.trans h2.symm))
    · exfalso
      exact hW₁neW₂ (Subgroup.map_injective g.injective (h1.trans h2.symm))
    · exact Or.inr ⟨h1, h2⟩
  have hswap : ∃ g ∈ A, W₁.map g.toMonoidHom = W₂ := ⟨t, ht, ht₁⟩
  have hKt : ⁅K, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro h
    have hKle : K ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (MulAut W)) :
        Set (MulAut W)) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hfixt : ∀ k ∈ K, MulAut.conj t k = k := by
      intro k hk
      have htk : t * k = k * t :=
        Subgroup.mem_centralizer_iff.mp (hKle hk) t (Subgroup.mem_zpowers t)
      rw [MulAut.conj_apply, htk]
      group
    have hKtmap : K.map (MulAut.conj t).toMonoidHom = K := by
      apply le_antisymm
      · intro y hy
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        show MulAut.conj t k ∈ K
        rw [hfixt k hk]
        exact hk
      · intro y hy
        exact Subgroup.mem_map.mpr ⟨y, hy, hfixt y hy⟩
    have hW₁t : (commSub ⊤ K).map t.toMonoidHom = commSub ⊤ K := by
      have hmap := CFSG.Quasithin.Asc81c.commSub_map_conj K t
      rw [hKtmap] at hmap
      exact hmap.symm
    rw [hKW] at hW₁t
    exact hW₁neW₂ (hW₁t.symm.trans ht₁)
  obtain ⟨hconc, hcount⟩ :=
    s168e3_cyc_conc (p := 7) (d := 3) (Or.inr ⟨rfl, rfl⟩) hinf hsup hrkW₁ hLn hperm hswap
      (B := B) (K := K) rfl rfl hBp hBc hKc hKW hKt
  refine ⟨K, hconc, hKc, ?_, hcount, ?_⟩
  · rw [hKW]; exact hrkW₁
  · intro r hr hr2 hr7
    by_contra hge
    push Not at hge
    obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt A
    have h1 : r ^ 2 ∣ Nat.card ↥E := by rw [hEcard]; exact pow_dvd_pow r hge
    have h2 : Nat.card ↥E ∣ Nat.card ↥A := Subgroup.card_dvd_of_le hEA
    exact s168e3_cyc_not_sq_dvd_294 hr hr7 (h1.trans (h2.trans hA_dvd294))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
