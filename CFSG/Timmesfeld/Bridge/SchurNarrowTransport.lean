module

public import CFSG.Timmesfeld.Bridge.Asc73Central
public import CFSG.Timmesfeld.Bridge.SchurNarrowBasic

public section

namespace CFSG.Timmesfeld.Bridge

open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem eq_one_of_mem_odd_of_mem_two {M S : Subgroup X} (hM : Odd (Nat.card M))
    (hS : IsPGroup 2 S) {g : X} (hgM : g ∈ M) (hgS : g ∈ S) : g = 1 := by
  obtain ⟨n, hn⟩ := hS ⟨g, hgS⟩
  have hg : g ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 := eq_one_of_pow_two_pow_of_odd hM (k := ⟨g, hgM⟩) (n := n)
    (Subtype.ext (by simpa using hg))
  simpa using congrArg Subtype.val h1

theorem sylow_le_of_odd_index {N : Subgroup X} [N.Normal] (hN : Odd N.index) (S : Sylow 2 X) :
    (S : Subgroup X) ≤ N := by
  intro s hs
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hodd : Odd (Nat.card (X ⧸ N)) := by rwa [Subgroup.index] at hN
  have h1 := eq_one_of_pow_two_pow_of_odd hodd (k := QuotientGroup.mk' N s) (n := n)
    (by rw [← map_pow, hsn, map_one])
  exact (QuotientGroup.eq_one_iff s).mp h1

theorem sylowBorelData_of_section {M N : Subgroup X} [N.Normal] [(M.subgroupOf N).Normal]
    (hM : Odd (Nat.card M)) (hN : Odd N.index)
    (hB : ∀ Q : Sylow 2 (N ⧸ M.subgroupOf N),
      SylowBorelData (N ⧸ M.subgroupOf N) (Q : Subgroup (N ⧸ M.subgroupOf N)))
    (S : Sylow 2 X) : SylowBorelData X S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := N ⧸ M.subgroupOf N
  have hSN := sylow_le_of_odd_index hN S
  set ρ : N →* B := QuotientGroup.mk' (M.subgroupOf N) with hρ
  set SN : Sylow 2 N := S.subtype hSN with hSNdef
  set Q : Sylow 2 B := SN.mapSurjective (QuotientGroup.mk'_surjective (M.subgroupOf N)) with hQ
  have hBQ := hB Q
  have hSNmem : ∀ a : N, a ∈ (SN : Subgroup N) ↔ (a : X) ∈ (S : Subgroup X) := fun a => by
    rw [hSNdef, Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  have hQmem : ∀ b : B, b ∈ (Q : Subgroup B) ↔ ∃ a : N, (a : X) ∈ (S : Subgroup X) ∧ ρ a = b := by
    intro b
    rw [hQ, Sylow.coe_mapSurjective]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hSNmem a).mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hSNmem a).mpr ha, rfl⟩
  have hρQ : ∀ a : N, (a : X) ∈ (S : Subgroup X) → ρ a ∈ (Q : Subgroup B) :=
    fun a ha => (hQmem _).mpr ⟨a, ha, rfl⟩
  have hinj : ∀ a b : N, (a : X) ∈ (S : Subgroup X) → (b : X) ∈ (S : Subgroup X) →
      ρ a = ρ b → a = b := by
    intro a b ha hb hab
    have hk : a⁻¹ * b ∈ M.subgroupOf N := QuotientGroup.eq.mp hab
    have hkS : ((a⁻¹ * b : N) : X) ∈ (S : Subgroup X) := by
      simpa using (S : Subgroup X).mul_mem ((S : Subgroup X).inv_mem ha) hb
    have h1 := eq_one_of_mem_odd_of_mem_two hM S.isPGroup' (Subgroup.mem_subgroupOf.mp hk) hkS
    have h2 : a⁻¹ * b = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp h2)
  have hcen : ∀ a : N, (a : X) ∈ (S : Subgroup X) →
      (CentralIn (S : Subgroup X) (a : X) ↔ CentralIn (Q : Subgroup B) (ρ a)) := by
    intro a ha
    constructor
    · rintro ⟨-, hc⟩
      refine ⟨hρQ a ha, fun q hq => ?_⟩
      obtain ⟨t, htS, rfl⟩ := (hQmem q).mp hq
      have htc : Commute t a := Subtype.ext (hc _ htS).eq
      exact htc.map ρ
    · rintro ⟨-, hc⟩
      refine ⟨ha, fun t ht => ?_⟩
      have htN : t ∈ N := hSN ht
      have h1 := (hc _ (hρQ ⟨t, htN⟩ ht)).eq
      rw [← map_mul, ← map_mul] at h1
      have h2 := hinj _ _ ((S : Subgroup X).mul_mem ht ha) ((S : Subgroup X).mul_mem ha ht) h1
      exact congrArg Subtype.val h2
  have hpre : ∀ b : B, b ∈ (Q : Subgroup B) → ∃ a : N, (a : X) ∈ (S : Subgroup X) ∧ ρ a = b :=
    fun b hb => (hQmem b).mp hb
  let σN : B → N := fun b => if h : b ∈ (Q : Subgroup B) then Classical.choose (hpre b h) else 1
  have hσN : ∀ b : B, b ∈ (Q : Subgroup B) →
      ((σN b : N) : X) ∈ (S : Subgroup X) ∧ ρ (σN b) = b := by
    intro b hb
    simp only [σN, dite_eq_left hb]
    exact Classical.choose_spec (hpre b hb)
  have hσρ : ∀ a : N, (a : X) ∈ (S : Subgroup X) → σN (ρ a) = a := fun a ha =>
    hinj _ _ (hσN _ (hρQ a ha)).1 ha (hσN _ (hρQ a ha)).2
  have hσmul : ∀ a ∈ (Q : Subgroup B), ∀ b ∈ (Q : Subgroup B), σN (a * b) = σN a * σN b := by
    intro a ha b hb
    have hab := (Q : Subgroup B).mul_mem ha hb
    refine hinj _ _ (hσN _ hab).1 ?_ ?_
    · exact (S : Subgroup X).mul_mem (hσN a ha).1 (hσN b hb).1
    · rw [map_mul, (hσN _ hab).2, (hσN a ha).2, (hσN b hb).2]
  obtain ⟨D, hDodd, hDN, htrans, hforms⟩ := hBQ.torus
  set D' : Subgroup N := D.comap ρ ⊓ Subgroup.normalizer ((SN : Subgroup N) : Set N) with hD'
  set Db : Subgroup X := D'.map N.subtype with hDb
  have hlift : ∀ d ∈ D, ∃ g : N, g ∈ D' ∧ ρ g = d := by
    intro d hd
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf N) d
    have hg₀ : ρ g₀ ∈ Subgroup.normalizer (((SN : Subgroup N).map ρ : Subgroup B) : Set B) := by
      have h := hDN hd
      rwa [hQ, Sylow.coe_mapSurjective] at h
    obtain ⟨k, hk, hkg⟩ := exists_ker_mul_mem_normalizer ρ SN hg₀
    have hρk : ρ (k * g₀) = ρ g₀ := by rw [map_mul, MonoidHom.mem_ker.mp hk, one_mul]
    refine ⟨k * g₀, ⟨?_, hkg⟩, hρk⟩
    change ρ (k * g₀) ∈ D
    rw [hρk]
    exact hd
  have hnorm : ∀ g ∈ D', (g : X) ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhN : h ∈ N
    · have := Subgroup.mem_normalizer_iff.mp hg.2 ⟨h, hhN⟩
      rw [hSNmem, hSNmem] at this
      exact this
    · constructor
      · intro hh
        exact absurd (hSN hh) hhN
      · intro hh
        exfalso
        apply hhN
        have hmem : (g : X) * h * (g : X)⁻¹ ∈ N := hSN hh
        have hgN : (g : X) ∈ N := g.2
        have : h = (g : X)⁻¹ * ((g : X) * h * (g : X)⁻¹) * (g : X) := by group
        rw [this]
        exact N.mul_mem (N.mul_mem (N.inv_mem hgN) hmem) hgN
  have hconjS : ∀ g ∈ D', ∀ s : X, s ∈ (S : Subgroup X) → (g : X)⁻¹ * s * g ∈ (S : Subgroup X) := by
    intro g hg s hs
    have h := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (hnorm g hg)) s).mp hs
    simpa using h
  refine ⟨?_, ?_, ?_, ?_, ⟨Db, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro a ha b hb
    have hc := hBQ.commutator_central _ (hρQ ⟨a, hSN ha⟩ ha) _ (hρQ ⟨b, hSN hb⟩ hb)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hc
    have hS' : (((⟨a, hSN ha⟩ : N) * ⟨b, hSN hb⟩ * (⟨a, hSN ha⟩ : N)⁻¹ * (⟨b, hSN hb⟩ : N)⁻¹ :
        N) : X) ∈ (S : Subgroup X) := by
      simpa using (S : Subgroup X).mul_mem ((S : Subgroup X).mul_mem
        ((S : Subgroup X).mul_mem ha hb) ((S : Subgroup X).inv_mem ha))
        ((S : Subgroup X).inv_mem hb)
    exact (hcen _ hS').mpr hc
  ·
    intro a ha
    have hc := hBQ.sq_central _ (hρQ ⟨a, hSN ha⟩ ha)
    rw [← map_mul] at hc
    have hS' : (((⟨a, hSN ha⟩ : N) * ⟨a, hSN ha⟩ : N) : X) ∈ (S : Subgroup X) := by
      simpa using (S : Subgroup X).mul_mem ha ha
    exact (hcen _ hS').mpr hc
  ·
    intro w hw
    have hwN := hSN hw.1
    have h1 := hBQ.center_sq _ ((hcen ⟨w, hwN⟩ hw.1).mp hw)
    rw [← map_mul, ← map_one ρ] at h1
    have h2 := hinj _ _ (by simpa using (S : Subgroup X).mul_mem hw.1 hw.1)
      (S : Subgroup X).one_mem h1
    simpa using congrArg Subtype.val h2
  ·
    obtain ⟨q, hq, hqc⟩ := hBQ.noncomm
    obtain ⟨t, htS, rfl⟩ := (hQmem q).mp hq
    exact ⟨t, htS, fun h => hqc ((hcen t htS).mp h)⟩
  ·
    have hcard : Nat.card Db = Nat.card D' :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [hcard]
    rcases Nat.even_or_odd (Nat.card D') with he | ho
    · exfalso
      obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 he.two_dvd
      have hρd : ρ (d : N) ∈ D := d.2.1
      have hdvd2 : orderOf (⟨ρ (d : N), hρd⟩ : D) ∣ 2 := by
        rw [Subgroup.orderOf_mk, ← hd]
        exact (orderOf_map_dvd ρ (d : N)).trans (Subgroup.orderOf_coe d).dvd
      have hdvdD : orderOf (⟨ρ (d : N), hρd⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
      have h1 : orderOf (⟨ρ (d : N), hρd⟩ : D) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
        · exact h
        · rw [h] at hdvdD
          exact absurd (_root_.even_iff_two_dvd.mpr hdvdD) (Nat.not_even_iff_odd.mpr hDodd)
      have hρd1 : ρ (d : N) = 1 := by
        have := orderOf_eq_one_iff.mp h1
        simpa using congrArg Subtype.val this
      have hdM : ((d : N) : X) ∈ M :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hρd1)
      have hd2 : ((d : N) : X) ^ 2 ^ 1 = 1 := by
        rw [pow_one, ← hd, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
        exact pow_orderOf_eq_one _
      have h3 := eq_one_of_pow_two_pow_of_odd hM (k := ⟨((d : N) : X), hdM⟩) (n := 1)
        (Subtype.ext (by simpa using hd2))
      have h4 : ((d : N) : X) = 1 := by simpa using congrArg Subtype.val h3
      have h5 : orderOf ((d : N) : X) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hd
      rw [h4, orderOf_one] at h5
      exact absurd h5 (by decide)
    · exact ho
  ·
    rintro _ ⟨g, hg, rfl⟩
    exact hnorm g hg
  ·
    intro w w' hw hw1 hw' hw'1
    have hwN := hSN hw.1
    have hw'N := hSN hw'.1
    have hρw := (hcen ⟨w, hwN⟩ hw.1).mp hw
    have hρw' := (hcen ⟨w', hw'N⟩ hw'.1).mp hw'
    have hne : ∀ v (hv : v ∈ (S : Subgroup X)), v ≠ 1 → ρ ⟨v, hSN hv⟩ ≠ 1 := by
      intro v hv hv1 h
      rw [← map_one ρ] at h
      have := hinj _ _ hv (S : Subgroup X).one_mem h
      exact hv1 (congrArg Subtype.val this)
    obtain ⟨d, hd, hdw⟩ := htrans _ _ hρw (hne w hw.1 hw1) hρw' (hne w' hw'.1 hw'1)
    obtain ⟨g, hg, hgd⟩ := hlift d hd
    refine ⟨(g : X), ⟨g, hg, rfl⟩, ?_⟩
    have hmem : (g : X)⁻¹ * w * g ∈ (S : Subgroup X) := hconjS g hg w hw.1
    have := hinj ((g⁻¹ * ⟨w, hwN⟩ * g : N)) ⟨w', hw'N⟩ (by simpa using hmem) hw'.1 (by
      rw [map_mul, map_mul, map_inv, hgd, hdw])
    simpa using congrArg Subtype.val this
  ·
    intro β hβ1 hβ2 hβ3 hβ4 hβ5
    let σ : B → X := fun b => ((σN b : N) : X)
    let βB : B → B → ZMod 2 := fun a b => β (σ a) (σ b)
    have hσS : ∀ b ∈ (Q : Subgroup B), σ b ∈ (S : Subgroup X) := fun b hb => (hσN b hb).1
    have hσmul' : ∀ a ∈ (Q : Subgroup B), ∀ b ∈ (Q : Subgroup B), σ (a * b) = σ a * σ b :=
      fun a ha b hb => by
        change ((σN (a * b) : N) : X) = ((σN a : N) : X) * ((σN b : N) : X)
        rw [hσmul a ha b hb]
        rfl
    have h0 := hforms βB
      (by
        intro a ha b hb c hc
        change β (σ (a * b)) (σ c) = β (σ a) (σ c) + β (σ b) (σ c)
        rw [hσmul' a ha b hb]
        exact hβ1 _ (hσS a ha) _ (hσS b hb) _ (hσS c hc))
      (by
        intro a ha b hb c hc
        change β (σ a) (σ (b * c)) = β (σ a) (σ b) + β (σ a) (σ c)
        rw [hσmul' b hb c hc]
        exact hβ2 _ (hσS a ha) _ (hσS b hb) _ (hσS c hc))
      (fun a ha => hβ3 _ (hσS a ha))
      (by
        intro a ha b hb
        refine hβ4 _ (hσS a ha) _ ?_
        have h := (hcen (σN b) (hσN b hb.1).1).mpr (by rw [(hσN b hb.1).2]; exact hb)
        exact h)
      (by
        intro d hd a ha b hb
        obtain ⟨g, hg, hgd⟩ := hlift d hd
        have hdQ : ∀ c ∈ (Q : Subgroup B), d⁻¹ * c * d ∈ (Q : Subgroup B) := by
          intro c hc
          have h := (Subgroup.mem_normalizer_iff.mp (hDN (D.inv_mem hd)) c).mp hc
          simpa using h
        have hconj : ∀ c ∈ (Q : Subgroup B), σ (d⁻¹ * c * d) = (g : X)⁻¹ * σ c * g := by
          intro c hc
          have h1 := hinj (σN (d⁻¹ * c * d)) (g⁻¹ * σN c * g) (hσN _ (hdQ c hc)).1
            (by simpa using hconjS g hg _ (hσS c hc))
            (by rw [(hσN _ (hdQ c hc)).2, map_mul, map_mul, map_inv, hgd, (hσN c hc).2])
          change ((σN (d⁻¹ * c * d) : N) : X) = _
          rw [h1]
          rfl
        change β (σ (d⁻¹ * a * d)) (σ (d⁻¹ * b * d)) = β (σ a) (σ b)
        rw [hconj a ha, hconj b hb]
        exact hβ5 _ ⟨g, hg, rfl⟩ _ (hσS a ha) _ (hσS b hb))
    intro a ha b hb
    have h := h0 _ (hρQ ⟨a, hSN ha⟩ ha) _ (hρQ ⟨b, hSN hb⟩ hb)
    change β (σ (ρ ⟨a, hSN ha⟩)) (σ (ρ ⟨b, hSN hb⟩)) = 0 at h
    have ea : σ (ρ ⟨a, hSN ha⟩) = a := by
      change ((σN (ρ ⟨a, hSN ha⟩) : N) : X) = a
      rw [hσρ _ ha]
    have eb : σ (ρ ⟨b, hSN hb⟩) = b := by
      change ((σN (ρ ⟨b, hSN hb⟩) : N) : X) = b
      rw [hσρ _ hb]
    rwa [ea, eb] at h
  ·
    refine le_trans hBQ.center_card (Nat.card_le_card_of_injective
      (fun w : {w : B // CentralIn (Q : Subgroup B) w} =>
        (⟨((σN w : N) : X), (hcen (σN w) (hσN w w.2.1).1).mpr
          (by rw [(hσN w w.2.1).2]; exact w.2)⟩ : {w : X // CentralIn (S : Subgroup X) w})) ?_)
    intro w w' h
    simp only [Subtype.mk.injEq] at h
    have h1 : σN (w : B) = σN (w' : B) := Subtype.ext h
    apply Subtype.ext
    rw [← (hσN w w.2.1).2, ← (hσN w' w'.2.1).2, h1]

end CFSG.Timmesfeld.Bridge
