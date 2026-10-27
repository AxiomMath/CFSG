module

public import CFSG.Sporadic.Schreier.TitsInv
public import CFSG.Sporadic.Schreier.TitsAbel
public import CFSG.Sporadic.Schreier.RuOrbit
public import CFSG.Quasithin.Recognition.RuRank3Defs
public meta import CFSG.Sporadic.Schreier.TitsInv
public meta import CFSG.Sporadic.Schreier.TitsAbel
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2264
public import Certificates.Certificate2266
public import Certificates.Certificate2268
public import Certificates.Certificate2270
public import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
public import Certificates.Certificate7051

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates

theorem orbit_eq_labels {n : ℕ} {gens : Array (Array ℕ)} {Gs : ℕ → Equiv.Perm (Fin n)}
    (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k)) (h : orbCheck n gens = true) (x : Fin n) :
    MulAction.orbit (genSubgroup n gens.size Gs) x =
      {y : Fin n | (orbLabels n gens).1[(y : ℕ)]! = (orbLabels n gens).1[(x : ℕ)]!} :=
  orbit_eq_label hrep h x

theorem orbit_eq_orbLab {n : ℕ} {gens : Array (Array ℕ)} {Gs : ℕ → Equiv.Perm (Fin n)}
    (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k)) (h : orbCheck n gens = true) (x : Fin n) :
    MulAction.orbit (genSubgroup n gens.size Gs) x =
      {y : Fin n | (orbLab n gens)[(y : ℕ)]! = (orbLab n gens)[(x : ℕ)]!} :=
  orbit_eq_labels hrep h x

theorem ncard_labelClass {n : ℕ} (lab : Array ℕ) (c : ℕ) :
    {y : Fin n | lab[(y : ℕ)]! = c}.ncard = labCount n lab c := by
  classical
  have e : {y : Fin n | lab[(y : ℕ)]! = c} =
      ((Finset.univ.filter fun y : Fin n => lab[(y : ℕ)]! = c) : Set (Fin n)) := by
    ext y
    simp
  rw [e, Set.ncard_coe_finset, labCount, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  apply Finset.card_bij (fun (y : Fin n) _ => (y : ℕ))
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp [hy, y.2]
  · intro a _ b _ h
    exact Fin.ext h
  · intro m hm
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hm
    exact ⟨⟨m, hm.1⟩, by simp [hm.2], rfl⟩

theorem titsPA_orbit_check :
    orbCheck 1755 titsPAGens = true ∧ labCount 1755 titsPALab titsPALab[0]! = 1 ∧
    titsPALab[1]! = titsPALab[2]! ∧ labCount 1755 titsPALab titsPALab[1]! = 2 ∧
    (allLt 1755 fun x => x == 0 || x == 1 || x == 2 ||
      decide (8 ≤ labCount 1755 titsPALab titsPALab[x]!)) = true ∧
    (titsGenArrs[1]!)[0]! = 0 :=
  Certificates.certificate7051

@[expose] noncomputable def titsPAGen (k : ℕ) : Equiv.Perm (Fin 1755) :=
  if k < 3 then titsSGen k else titsGen 1

theorem titsPAGens_rep :
    ∀ k < titsPAGens.size, Rep 1755 titsPAGens[k]! (titsPAGen k) := by
  intro k hk
  have hk4 : k < 4 := by simpa [titsPAGens] using hk
  interval_cases k
  · simpa [titsPAGens, titsPAGen] using titsSGen_rep (by norm_num : 0 < 3)
  · simpa [titsPAGens, titsPAGen] using titsSGen_rep (by norm_num : 1 < 3)
  · simpa [titsPAGens, titsPAGen] using titsSGen_rep (by norm_num : 2 < 3)
  · simpa [titsPAGens, titsPAGen] using titsGen1_rep

theorem titsSGen_mem_titsPA
    {i : ℕ} (hi : i < 3) :
    titsSGen i ∈ titsPA :=
  Or.inl (titsSGen_mem hi)

theorem titsGen1_mem_titsPA :
    titsGen 1 ∈ titsPA :=
  Or.inr (by rw [mul_inv_cancel]; exact one_mem _)

theorem genSubgroup_titsPA :
    genSubgroup 1755 titsPAGens.size titsPAGen = titsPA := by
  apply le_antisymm
  · rw [genSubgroup, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk4 : k < 4 := by simpa [titsPAGens] using hk
    by_cases h3 : k < 3
    · simp only [titsPAGen, h3, ↓reduceIte]
      exact titsSGen_mem_titsPA h3
    · simp only [titsPAGen, h3, ↓reduceIte]
      exact titsGen1_mem_titsPA
  · have hS : titsS ≤ genSubgroup 1755 titsPAGens.size titsPAGen := by
      rw [titsS_eq_closure, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, by simp [titsPAGens]; omega, by
        simp [titsPAGen, i.2]⟩
    have ha : titsGen 1 ∈ genSubgroup 1755 titsPAGens.size titsPAGen :=
      Subgroup.subset_closure ⟨3, by simp [titsPAGens], by simp [titsPAGen]⟩
    rintro x (hx | hx)
    · exact hS hx
    · have := mul_mem (hS hx) ha
      rwa [inv_mul_cancel_right] at this

theorem orbit_titsPA
    (x : Fin 1755) :
    MulAction.orbit titsPA x = {y : Fin 1755 | titsPALab[(y : ℕ)]! = titsPALab[(x : ℕ)]!} := by
  rw [← genSubgroup_titsPA]
  exact orbit_eq_orbLab titsPAGens_rep titsPA_orbit_check.1 x

theorem ncard_orbit_titsPA
    (x : Fin 1755) :
    (MulAction.orbit titsPA x).ncard = labCount 1755 titsPALab titsPALab[(x : ℕ)]! := by
  rw [orbit_titsPA, ncard_labelClass]

theorem titsPA_fixed_iff
    (x : Fin 1755) :
    (∀ g ∈ titsPA, g x = x) ↔ x = 0 := by
  constructor
  · intro h
    have hsing : MulAction.orbit titsPA x = {x} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact h g g.2
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact MulAction.mem_orbit_self _
    have h1 : labCount 1755 titsPALab titsPALab[(x : ℕ)]! = 1 := by
      rw [← ncard_orbit_titsPA, hsing, Set.ncard_singleton]
    by_contra hx0
    have := allLt_spec titsPA_orbit_check.2.2.2.2.1 x.2
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with ((h0 | h6) | h9) | h8
    · exact hx0 (Fin.ext h0)
    · rw [show (x : ℕ) = 1 from h6, titsPA_orbit_check.2.2.2.1] at h1
      exact absurd h1 (by norm_num)
    · rw [show (x : ℕ) = 2 from h9, ← titsPA_orbit_check.2.2.1,
        titsPA_orbit_check.2.2.2.1] at h1
      exact absurd h1 (by norm_num)
    · rw [h1] at h8
      omega
  · rintro rfl g hg
    have h2 : titsGen 1 0 = 0 := by
      apply Fin.ext
      rw [← titsGen1_rep 0]
      exact titsPA_orbit_check.2.2.2.2.2
    rcases hg with hg | hg
    · exact (mem_titsH_iff.1 (titsS_le_titsH hg)).2
    · have h1 : (g * (titsGen 1)⁻¹) 0 = 0 := (mem_titsH_iff.1 (titsS_le_titsH hg)).2
      rw [Equiv.Perm.mul_apply] at h1
      have : (titsGen 1)⁻¹ 0 = 0 := by
        rw [Equiv.Perm.inv_eq_iff_eq, h2]
      rwa [this] at h1

theorem titsA_pretransitive :
    MulAction.IsPretransitive titsA (Fin 1755) := by
  have := titsD_pretransitive
  refine ⟨fun x y => ?_⟩
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq titsD x y
  exact ⟨⟨d, titsD_le_titsA d.2⟩, hd⟩

theorem card_stabilizer_titsA (x : Fin 1755) :
    Nat.card (MulAction.stabilizer titsA x) = 20480 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer titsA x)
  have hi : (MulAction.stabilizer titsA x).index = 1755 := by
    have := titsA_pretransitive
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hi, card_titsA] at h
  omega

theorem fixes_zero_of_card
    {H : Subgroup (Equiv.Perm (Fin 1755))} (hPA : titsPA ≤ H)
    (hH : Nat.card H = 20480) : ∀ h ∈ H, h 0 = 0 := by
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨h₀, hh₀, hh₀0⟩ := hne
  set O := MulAction.orbit H (0 : Fin 1755) with hO
  have hle : titsPA.subgroupOf H ≤ MulAction.stabilizer H (0 : Fin 1755) := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MulAction.mem_stabilizer_iff]
    exact (titsPA_fixed_iff 0).2 rfl _ hg
  have hdvd : 4096 ∣ Nat.card (MulAction.stabilizer H (0 : Fin 1755)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_subgroupOf_eq hPA, card_titsPA] at this
  have hcard : O.ncard * Nat.card (MulAction.stabilizer H (0 : Fin 1755)) = 20480 := by
    rw [← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index, hH]
  have hO5 : O.ncard ∣ 5 := by
    obtain ⟨m, hm⟩ := hdvd
    rw [hm] at hcard
    refine ⟨m, ?_⟩
    have : 4096 * (O.ncard * m) = 4096 * 5 := by
      rw [show (4096 : ℕ) * 5 = 20480 by norm_num, ← hcard]
      ring
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) this).symm
  have hmem0 : (0 : Fin 1755) ∈ O := MulAction.mem_orbit_self _
  have hmem1 : h₀ 0 ∈ O := ⟨⟨h₀, hh₀⟩, rfl⟩
  have hO1 : O.ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have e1 : (0 : Fin 1755) = a := by rw [ha] at hmem0; exact hmem0
    have e2 : h₀ 0 = a := by rw [ha] at hmem1; exact hmem1
    exact hh₀0 (e2.trans e1.symm)
  have hO5' : O.ncard = 5 := by
    rcases (Nat.dvd_prime (by norm_num)).1 hO5 with h | h
    · exact absurd h hO1
    · exact h
  have hsub : O \ {0} ⊆ {1, 2} := by
    intro x hx
    obtain ⟨hxO, hx0⟩ := hx
    rw [Set.mem_singleton_iff] at hx0
    have horb : MulAction.orbit titsPA x ⊆ O \ {0} := by
      rintro _ ⟨g, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := hxO
        have hk' : k • (0 : Fin 1755) = x := hk
        refine ⟨⟨g, hPA g.2⟩ * k, ?_⟩
        show (⟨g, hPA g.2⟩ * k : H) • (0 : Fin 1755) = g • x
        rw [mul_smul, hk']
        rfl
      · intro hg0
        apply hx0
        have hg0' : (g : Equiv.Perm (Fin 1755)) x = 0 := hg0
        have hfix : ((g : Equiv.Perm (Fin 1755))⁻¹) 0 = 0 :=
          (titsPA_fixed_iff 0).2 rfl _ (inv_mem g.2)
        have hx : x = ((g : Equiv.Perm (Fin 1755))⁻¹) 0 := by
          rw [← hg0', ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
        rw [hx, hfix]
    have hle4 : (MulAction.orbit titsPA x).ncard ≤ 4 := by
      have := Set.ncard_le_ncard horb (Set.toFinite _)
      rwa [Set.ncard_sdiff_singleton_of_mem hmem0, hO5'] at this
    rw [ncard_orbit_titsPA] at hle4
    have := allLt_spec titsPA_orbit_check.2.2.2.2.1 x.2
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with ((h0 | h6) | h9) | h8
    · exact absurd (Fin.ext h0) hx0
    · exact Or.inl (Fin.ext h6)
    · exact Or.inr (Fin.ext h9)
    · omega
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_sdiff_singleton_of_mem hmem0, hO5', Set.ncard_pair (by decide)] at this
  omega

theorem eq_stabilizer_zero_of_card
    {H : Subgroup titsA}
    (hP : titsPA.subgroupOf titsA ≤ H)
    (hH : Nat.card H = 20480) : H = MulAction.stabilizer titsA (0 : Fin 1755) := by
  have hPA : titsPA ≤ H.map titsA.subtype := by
    intro g hg
    exact ⟨⟨g, titsPA_le_titsA hg⟩, hP (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hH' : Nat.card (H.map titsA.subtype) = 20480 := by
    rw [← hH]
    exact Nat.card_congr (Subgroup.equivMapOfInjective H _ titsA.subtype_injective).toEquiv.symm
  have hfix := fixes_zero_of_card hPA hH'
  apply Subgroup.eq_of_le_of_card_ge
  · intro h hh
    rw [MulAction.mem_stabilizer_iff]
    exact hfix _ ⟨h, hh, rfl⟩
  · rw [hH, card_stabilizer_titsA]

theorem card_titsPASylow :
    Nat.card (titsPASylow : Subgroup titsA) = 4096 := by
  show Nat.card (titsPA.subgroupOf titsA) = 4096
  rw [card_subgroupOf_eq titsPA_le_titsA, card_titsPA]

theorem card_sylow_two_titsA
    (Q : Sylow 2 titsA) :
    Nat.card (Q : Subgroup titsA) = 4096 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity titsPASylow, card_titsPASylow]

theorem exists_eq_stabilizer_of_card
    {H : Subgroup titsA}
    (hH : Nat.card H = 20480) :
    ∃ x : Fin 1755, H = MulAction.stabilizer titsA x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := 12)
    (by rw [hH]; norm_num)
  set K' : Subgroup titsA := K.map H.subtype with hK'
  have hcardK' : Nat.card K' = 4096 := by
    rw [hK', ← Nat.card_congr (Subgroup.equivMapOfInjective K _ H.subtype_injective).toEquiv, hK]
    norm_num
  have hpK' : IsPGroup 2 K' := IsPGroup.of_card (n := 12) (by rw [hcardK']; norm_num)
  obtain ⟨Q, hKQ⟩ := hpK'.exists_le_sylow
  have hQeq : K' = Q := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcardK', card_sylow_two_titsA])
  have hQ : (Q : Subgroup titsA) ≤ H := by
    rw [← hQeq, hK']
    exact Subgroup.map_subtype_le K
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsA titsPASylow Q
  set H' := H.map (MulAut.conj g⁻¹).toMonoidHom with hH'
  have hP : titsPA.subgroupOf titsA ≤ H' := by
    intro p hp
    refine ⟨g * p * g⁻¹, hQ ?_, by simp; group⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨p, hp, rfl⟩
  have hcard' : Nat.card H' = 20480 := by
    rw [← hH]
    exact Nat.card_congr (Subgroup.equivMapOfInjective H _ (MulAut.conj g⁻¹).injective).toEquiv.symm
  have e := eq_stabilizer_zero_of_card hP hcard'
  refine ⟨g • (0 : Fin 1755), ?_⟩
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← e, hH', Subgroup.map_map]
  conv_lhs => rw [← Subgroup.map_id H]
  congr 1
  ext h
  simp

theorem normalizer_titsPA_le
    {g : Equiv.Perm (Fin 1755)}
    (hg : g ∈ Subgroup.normalizer (titsPA : Set (Equiv.Perm (Fin 1755)))) : g 0 = 0 := by
  apply (titsPA_fixed_iff (g 0)).1
  intro p hp
  have hp' : g⁻¹ * p * g ∈ titsPA := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) p).1 hp
    rwa [inv_inv] at this
  have := (titsPA_fixed_iff 0).2 rfl _ hp'
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at this
  have := congrArg g this
  rwa [← Equiv.Perm.mul_apply g g⁻¹, mul_inv_cancel, Equiv.Perm.one_apply] at this

theorem titsA_normalizer_titsPA_le
    {n : titsA}
    (hn : n ∈ Subgroup.normalizer ((titsPASylow : Subgroup titsA) : Set titsA)) :
    n • (0 : Fin 1755) = 0 := by
  apply normalizer_titsPA_le
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    have := (Subgroup.mem_normalizer_iff.1 hn ⟨p, titsPA_le_titsA hp⟩).1
      (by show _ ∈ titsPA.subgroupOf titsA; rw [Subgroup.mem_subgroupOf]; exact hp)
    change _ ∈ titsPA.subgroupOf titsA at this
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hp
    have hpA : p ∈ titsA := by
      have := mul_mem (mul_mem (inv_mem n.2) (titsPA_le_titsA hp)) n.2
      simpa [mul_assoc] using this
    have := (Subgroup.mem_normalizer_iff.1 hn ⟨p, hpA⟩).2
      (by show _ ∈ titsPA.subgroupOf titsA; rw [Subgroup.mem_subgroupOf]; exact hp)
    change _ ∈ titsPA.subgroupOf titsA at this
    rw [Subgroup.mem_subgroupOf] at this
    exact this

theorem isSylowTwoParabolic_of_card
    {F : Type*} [Group F]
    (ψ : F ≃* titsA) {P : Subgroup F}
    (hP : Nat.card P = 2 ^ 12 * 5) : IsSylowTwoParabolic P := by
  have hP' : Nat.card (P.map ψ.toMonoidHom) = 20480 := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective P _ ψ.injective).toEquiv, hP]
    norm_num
  obtain ⟨x, hx⟩ := exists_eq_stabilizer_of_card hP'
  have := titsA_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsA (0 : Fin 1755) x
  have hle : ((g • titsPASylow : Sylow 2 titsA) : Subgroup titsA) ≤ ψ.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top_of_surjective _ ψ.surjective]
    exact le_top
  have hinj : Function.Injective ψ.toMonoidHom := fun a b h => ψ.injective h
  refine ⟨(g • titsPASylow).comapOfInjective ψ.toMonoidHom hinj hle, ?_⟩
  intro f hf
  have hψf : g⁻¹ * ψ f * g ∈
      Subgroup.normalizer ((titsPASylow : Subgroup titsA) : Set titsA) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    have key : ∀ y : titsA, y ∈ (titsPASylow : Subgroup titsA) ↔
        g * y * g⁻¹ ∈ ((g • titsPASylow : Sylow 2 titsA) : Subgroup titsA) := by
      intro y
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y', hy', e⟩
        have : y' = y := by
          simpa [MulAut.conj_apply] using e
        rwa [← this]
    rw [key, key (g⁻¹ * ψ f * g * p * (g⁻¹ * ψ f * g)⁻¹)]
    have hf' := Subgroup.mem_normalizer_iff.1 hf (ψ.symm (g * p * g⁻¹))
    have e1 : ∀ y : titsA, ψ.symm y ∈ ((g • titsPASylow).comapOfInjective ψ.toMonoidHom hinj
        hle : Subgroup F) ↔ y ∈ ((g • titsPASylow : Sylow 2 titsA) : Subgroup titsA) := by
      intro y
      change ψ.symm y ∈ ((g • titsPASylow : Sylow 2 titsA) : Subgroup titsA).comap
        ψ.toMonoidHom ↔ _
      rw [Subgroup.mem_comap]
      simp
    rw [e1] at hf'
    have e2 : f * ψ.symm (g * p * g⁻¹) * f⁻¹ = ψ.symm (ψ f * (g * p * g⁻¹) * (ψ f)⁻¹) := by
      apply ψ.injective
      simp
    rw [e2, e1] at hf'
    rw [hf']
    constructor <;> intro h <;> simpa [mul_assoc] using h
  have hfix := titsA_normalizer_titsPA_le hψf
  have hmem : ψ f ∈ MulAction.stabilizer titsA x := by
    rw [MulAction.mem_stabilizer_iff, ← hg]
    have : (g⁻¹ * ψ f * g) • (0 : Fin 1755) = 0 := hfix
    rw [mul_smul, mul_smul] at this
    have := congrArg (g • ·) this
    simpa [smul_smul] using this
  rw [← hx] at hmem
  obtain ⟨f', hf', e⟩ := hmem
  have : f' = f := ψ.injective e
  rwa [← this]

end CFSG.Quasithin.RuRank3
