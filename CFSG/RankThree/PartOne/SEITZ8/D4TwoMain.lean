module

public import CFSG.RankThree.PartOne.SEITZ8.D4Main
public import CFSG.RankThree.PartOne.SEITZ8.D4TwoCase
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
public import CFSG.RankThree.PartOne.SEITZ8.D4TwoNF

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K]

section FieldData

variable [Finite K]

theorem field_data_low {f0 p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf0 : 1 ≤ f0)
    (hK : Nat.card K = 2 ^ (3 * f0 * p)) {σ δ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ (f0 * p)) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * f0)) :
    ∃ (k : Subfield K) (F0 : Subfield (fixedField σ.toRingHom)),
      (∀ c ∈ k, δ c = c) ∧ (∀ c, δ c = c → c ∈ k) ∧ Rat3 σ.toRingHom k ∧
      (∀ c : fixedField σ.toRingHom, c ∈ F0 ↔ (c : K) ∈ k) ∧
      Nat.card (fixedField σ.toRingHom) = Nat.card F0 ^ p ∧ Nat.card F0 = 2 ^ f0 ∧
      (∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}) := by
  classical
  have hp3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨-, -, -, hk, hord⟩ := CFSG.RankThree.Chevalley.triality_canonical_field_facts
    Nat.prime_two (by omega : 1 ≤ f0) hp.two_le hp3 hK hσ hδ
  set k : Subfield K := fixSubfield δ with hkdef
  have hcardF : Nat.card (fixedField σ.toRingHom) = 2 ^ (f0 * p) :=
    card_fixedField (by nlinarith) (by rw [hK, ← pow_mul]; congr 1; ring) (fun c => hσ c)
  set F0 : Subfield (fixedField σ.toRingHom) := k.comap (fixedField σ.toRingHom).subtype
    with hF0def
  have hF0mem : ∀ c : fixedField σ.toRingHom, c ∈ F0 ↔ (c : K) ∈ k := fun c => Iff.rfl
  set σ0 := fixSubfieldRestrict σ δ with hσ0
  have hS := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega : 1 ≤ 3 * f0) hk σ0).2
  rw [hord, Nat.mul_div_cancel_left f0 (by norm_num : 0 < 3)] at hS
  have hF0card : Nat.card F0 = 2 ^ f0 := by
    rw [← hS]
    exact Nat.card_congr ⟨fun x => ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩,
      fun y => ⟨⟨y.1.1, congrArg Subtype.val y.2⟩, y.1.2⟩, fun x => rfl, fun y => rfl⟩
  have hcard : Nat.card (fixedField σ.toRingHom) = Nat.card F0 ^ p := by
    rw [hcardF, hF0card, ← pow_mul]
  have hstab : ∀ a ∈ k, σ.toRingHom a ∈ k := fun a ha => by
    have ha' : δ a = a := ha
    have e : σ a = a ^ 2 ^ (f0 * p) := hσ a
    show δ (σ a) = σ a
    rw [e, map_pow, ha']
  have hkcard : Nat.card k = (2 ^ f0) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hσk : ∀ a : k, (RingHom.restrict σ.toRingHom k k hstab) a = a ^ (2 ^ f0) ^ (p % 3) := by
    intro a
    apply Subtype.ext
    show σ (a : K) = ((a ^ (2 ^ f0) ^ (p % 3) : k) : K)
    rw [hσ, sigma_pow_on_fix hk a.2]
    rfl
  have hind : MonoInd k (RingHom.restrict σ.toRingHom k k hstab) := by
    have : Fintype k := Fintype.ofFinite k
    exact monoInd_of_frobenius (RingHom.restrict σ.toRingHom k k hstab) (q := 2 ^ f0)
      (by calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f0 := Nat.pow_le_pow_right (by norm_num) (by omega))
      (by rw [← Nat.card_eq_fintype_card, hkcard]) hj hσk
  have hspan := span_of_card (fixedField σ.toRingHom) k (Q := 2 ^ f0) (p := p)
    (by calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f0 := Nat.pow_le_pow_right (by norm_num) (by omega)) hp (by omega)
    (by rw [hcardF, ← pow_mul]) hkcard (by rw [hK, ← pow_mul]; congr 1; ring)
  exact ⟨k, F0, fun c hc => hc, fun c hc => hc, ⟨hstab, hind⟩, hF0mem, hcard, hF0card, hspan⟩

end FieldData

structure D4SetupLow (σ δ : K →+* K) (k : Subfield K)
    (F0 : Subfield (fixedField σ)) (d q : ℕ) : Prop where
  hσ3 : ∀ c, σ (σ (σ c)) = c
  hcomm : ∀ c, δ (σ c) = σ (δ c)
  hfix : ∀ c ∈ k, δ c = c
  hkδ : ∀ c, δ c = c → c ∈ k
  rat : Rat3 σ k
  hF0 : ∀ c : fixedField σ, c ∈ F0 ↔ (c : K) ∈ k
  prime : d.Prime
  ne2 : d ≠ 2
  card : Nat.card (fixedField σ) = Nat.card F0 ^ d
  hF0card : Nat.card F0 = 2
  four : 4 ∣ Nat.card (fixedField σ)
  hne : ∃ a, σ a ≠ a
  span : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}
  q2 : 2 ≤ q
  hKq : Nat.card K = q ^ 3
  hσq : ∀ c, σ c = c ^ q
  stab : ∀ g : twistedGroup σ, ∃ g' : twistedGroup σ,
    ((g' : adjointGroup d4 K) : ModGL d4 K) =
      Units.map (entrywiseHom δ) ((g : adjointGroup d4 K) : ModGL d4 K)

section Core

variable [CharP K 2] [Finite K]
  {σ δ : K →+* K} {k : Subfield K} {F0 : Subfield (fixedField σ)} {d q : ℕ}

theorem exists_bad_entry_low (S : D4SetupLow σ δ k F0 d q) (g : twistedGroup σ)
    (hg : g ∉ Rg σ δ) :
    ∃ r ∈ Rδ σ δ, ∃ r' ∈ Rδ σ δ,
      coordAt (d4Root 23) ((r * (g : adjointGroup d4 K) * r') • (rv 22 : RootModule d4 K)) ∉ k := by
  have hSpan := spanHyp_Rδ S.hσ3 S.hcomm S.hfix S.rat
  by_contra hcon
  push Not at hcon
  have hrat := ratMod_of_hcon hSpan (g : adjointGroup d4 K) hcon
  have hbasis := fun b => ratMod_basis hSpan hrat b
  obtain ⟨g', hg'⟩ := S.stab g
  have hcols : ∀ b : Label d4, (g' : adjointGroup d4 K) •
      (Finsupp.single b (1 : K) : RootModule d4 K) =
        Finsupp.mapRange δ δ.map_zero ((g : adjointGroup d4 K) •
          (Finsupp.single b (1 : K) : RootModule d4 K)) := by
    intro b
    rw [smul_eq_end, hg']
    show entrywise δ _ (Finsupp.single b 1) = _
    rw [entrywise_single]
    rfl
  have heq := eq_of_ratMod S.q2 S.hKq S.hσq δ S.hfix g g' hcols hbasis
  apply hg
  rw [mem_Rg, ← hg', heq]

theorem closure_eq_top_low (S : D4SetupLow σ δ k F0 d q) (g : twistedGroup σ)
    (hg : g ∉ Rg σ δ) :
    Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
      (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
        Set (twistedGroup σ))) = ⊤ := by
  set H : Subgroup (twistedGroup σ) := Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
    (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
      Set (twistedGroup σ))) with hH
  have hRH : Rg σ δ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : (Rg σ δ).map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hSp := spanHyp_Rδ S.hσ3 S.hcomm S.hfix S.rat
  set Hs : Subgroup (adjointGroup d4 K) := H.map (twistedGroup σ).subtype with hHs
  have hRs : ∀ x ∈ Rδ σ δ, x ∈ Hs := fun x hx => ⟨⟨x, hx.1⟩, hRH hx, rfl⟩
  have hConj : ∀ x ∈ Rδ σ δ, (g : adjointGroup d4 K) * x * (g : adjointGroup d4 K)⁻¹ ∈ Hs :=
    fun x hx => ⟨g * ⟨x, hx.1⟩ * g⁻¹, hRgH ⟨⟨x, hx.1⟩, hx, by simp [MulAut.conj_apply]⟩, rfl⟩
  have hRat : RatH σ k Hs := ⟨fun a ha => hRs _ (hSp.A a ha), hRs _ hSp.x2, hRs _ hSp.y2,
    hRs _ hSp.n0, hRs _ hSp.n1⟩
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_low S g hg
  set ρ : twistedGroup σ := ⟨r, hr.1⟩ with hρdef
  set ρ' : twistedGroup σ := ⟨r', hr'.1⟩ with hρ'def
  have hcoe : ((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) =
      r * (g : adjointGroup d4 K) * r' := rfl
  have hne0 : coordAt (d4Root 23) (((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) •
      (rv 22 : RootModule d4 K)) ≠ 0 := by
    rw [hcoe]
    intro h
    exact hbad (h ▸ k.zero_mem)
  obtain ⟨c, μ, hc1, hc0, hc3, hc7, hμσ, hμ, hyy⟩ := normal_form S.hσ3 (ρ * g * ρ') hne0
  have hμk : μ ∉ k := by
    rw [hμ, hcoe]
    exact hbad
  have h22 : xd 22 (1 : K) ∈ Rδ σ δ := by
    have e : Wt * xd 2 (1 : K) * Wt⁻¹ = xd 22 1 := Wt_xB 1
    have := (Rδ σ δ).mul_mem ((Rδ σ δ).mul_mem ((Rδ σ δ).mul_mem hSp.n0 hSp.n1) hSp.x2)
      ((Rδ σ δ).inv_mem ((Rδ σ δ).mul_mem hSp.n0 hSp.n1))
    rwa [show weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) *
        weylElement d4 K (nd 3)) = Wt from rfl, e] at this
  have hy : ordT σ c * xd 23 μ * (ordT σ c)⁻¹ ∈ Hs := by
    have h1 := hyy 1
    rw [mul_one, hcoe] at h1
    rw [← h1]
    rw [show r * (g : adjointGroup d4 K) * r' * xd 22 1 * (r * (g : adjointGroup d4 K) * r')⁻¹ =
      r * ((g : adjointGroup d4 K) * (r' * xd 22 1 * r'⁻¹) * (g : adjointGroup d4 K)⁻¹) * r⁻¹ by
        group]
    exact Hs.mul_mem (Hs.mul_mem (hRs _ hr) (hConj _ ((Rδ σ δ).mul_mem
      ((Rδ σ δ).mul_mem hr' h22) ((Rδ σ δ).inv_mem hr')))) (Hs.inv_mem (hRs _ hr))
  have hX := core_cases S.hσ3 S.hne S.span δ S.hcomm S.hfix S.hkδ S.hF0card S.hF0 S.prime S.ne2
    S.card hRat hc1 hc0 hc3 hc7 hμσ hμk hy
  have hn0 : nHat σ (ng 0) ∈ H := hRH (by
    rw [mem_Rg, nHat_val, nHatE_zero]
    exact hSp.n0.2)
  have hn1 : nHat σ (ng 1) ∈ H := hRH (by
    rw [mem_Rg, nHat_val, nHatE_one]
    exact hSp.n1.2)
  have hA : ∀ a ∈ k, slShort σ S.hσ3 (sl2Upper a) ∈ H := fun a ha => hRH (by
    rw [mem_Rg, slShort_upper_xA σ S.hσ3 a]
    exact (hSp.A a ha).2)
  have hlong : ∀ c : fixedField σ, psiB σ S.hσ3 (sl2Upper c) ∈ H := by
    intro c
    obtain ⟨h, hh, hhe⟩ := hX c
    have : h = psiB σ S.hσ3 (sl2Upper c) := Subtype.ext (by
      rw [show ((h : twistedGroup σ) : adjointGroup d4 K) = xH (c : K) from hhe,
        psiB_upper σ S.hσ3 c])
    rwa [← this]
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_one (L := fixedField σ) S.four
  have hHtop : H = ⊤ := eq_top_of_long S.hσ3 k hn0 hn1 hlong hA ((s : fixedField σ) : K)
    (s : fixedField σ).2 (fun h => hs0 (Subtype.ext h)) (fun h => hs1 (Subtype.ext h)) S.span
  exact hHtop

end Core

section Pair

variable {K : Type} [Field K] [Finite K]

theorem pair_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ (1 * p)) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ (1 * p))
    {δ : K ≃+* K} (hδ : ∀ c, δ c = c ^ 2 ^ (3 * 1))
    (g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hne : (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map
        (MulAut.conj g).toMonoidHom ≠ fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) :
    Subgroup.closure ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∪
      ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊤ := by
  have hK' : Nat.card K = 2 ^ (3 * 1 * p) := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3 * 1 * p) (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))
    hK'
  obtain ⟨k, F0, hfix, hkδ, hrat, hF0, hcard, hF0card, hspan⟩ :=
    field_data_low hp hp5 le_rfl hK' hσ hδ
  have hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ (1 * p)) := hσ
  have hq2 : 2 ≤ 2 ^ (1 * p) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (1 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := sigma_three_of_card hK hσq
  have hC0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two (f := 1 * p) (by omega) K hK
      σ.toRingHom hσq).2.2.1.symm.trans
      (commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 hK hσq)
  have hcardF : Nat.card (fixedField σ.toRingHom) = 2 ^ (1 * p) :=
    card_fixedField (by omega) hK (fun c => hσ c)
  have hne' : ∃ a, σ.toRingHom a ≠ a := by
    by_contra h
    push Not at h
    have hall : ∀ a : K, a ∈ fixedField σ.toRingHom := fun a => h a
    have e : Nat.card (fixedField σ.toRingHom) = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hcardF, hK] at e
    have h1 : 2 ^ (1 * p) < (2 ^ (1 * p)) ^ 3 := by
      calc 2 ^ (1 * p) = (2 ^ (1 * p)) ^ 1 := by rw [pow_one]
        _ < (2 ^ (1 * p)) ^ 3 := Nat.pow_lt_pow_right (by
          calc 1 < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (1 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
    omega
  have h4 : 4 ∣ Nat.card (fixedField σ.toRingHom) := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ (1 * p) := pow_dvd_pow 2 (by omega)
  have S : D4SetupLow σ.toRingHom δ.toRingHom k F0 p (2 ^ (1 * p)) :=
    { hσ3 := hσ3
      hcomm := fun c => by
        show δ (σ c) = σ (δ c)
        rw [hσ, hσ, map_pow]
      hfix := hfix
      hkδ := hkδ
      rat := hrat
      hF0 := hF0
      prime := hp
      ne2 := by omega
      card := hcard
      hF0card := by rw [hF0card]; norm_num
      four := h4
      hne := hne'
      span := hspan
      q2 := hq2
      hKq := hK
      hσq := hσq
      stab := stab_of_bridge σ δ hC0 }
  have hg : eGamma hC0 g ∉ Rg σ.toRingHom δ.toRingHom := fun h =>
    hne (map_conj_eq_of_mem ((mem_fixedSubgroup_iff σ δ hC0 g).2 h))
  exact closure_transport (eGamma hC0) _ _ (mem_fixedSubgroup_iff σ δ hC0) g
    (closure_eq_top_low S (eGamma hC0 g) hg)

end Pair

section Final

open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)



theorem subfieldPairD4Two_holds : SubfieldPairD4Two := by
  intro p hp hp5 _ K _ _ hK σ hσ δ hδ g hne
  classical
  have hK3 : Nat.card K = 2 ^ (3 * p) := by rw [hK, ← pow_mul, mul_comm]
  have hf3 : 1 ≤ 3 * p := by omega
  obtain ⟨φ, hφ, hφord, -, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf3 hK3
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf3 : p ∣ 3 * p := dvd_mul_left p 3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * 1) = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 2 ^ (3 * 1) := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord]; exact ⟨p, by ring⟩), hφord]
    omega
  have hzp : Subgroup.zpowers δ = Subgroup.zpowers δc :=
    zpowers_ringEquiv_eq_of_orderOf Nat.prime_two hf3 hK3 hδ hδcord
  have hfix : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) :=
    fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ) hzp
  rw [hfix] at hne ⊢
  have hKe : Nat.card K = (2 ^ (1 * p)) ^ 3 := by rw [hK, one_mul]
  have hσe : ∀ c, σ c = c ^ 2 ^ (1 * p) := fun c => by rw [hσ, one_mul]
  exact pair_two hp hp5 hKe hσe hδc g hne

end Final

end CFSG.RankThree.PartOne.SEITZ8
