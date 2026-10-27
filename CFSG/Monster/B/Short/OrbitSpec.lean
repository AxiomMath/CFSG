module

public import Certificates.Data.CFSGNative.MonsterB.Short
public import CFSG.Monster.VisCert.FrameSpec

public section

namespace CFSG.Monster.B.Short

open CFSG.Monster.VisCert CFSG.Monster.VisCert.Native CFSG.Monster.B.Short.Native

@[expose] def shortFound (T : ShortTables) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.klev v ≠ 0

structure ShortFacts (T : ShortTables) : Prop where
  point : ∀ v < 2 ^ 24, shortPointOK T v = true
  card_found : (shortFound T).card = shortCount

theorem shortFacts_of_check {T : ShortTables} {chunks : ℕ} (hc : 0 < chunks)
    (h : shortCheck T chunks = true) : ShortFacts T := by
  simp only [shortCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hpar, hcount⟩ := h
  refine ⟨parAll_spec hc hpar, ?_⟩
  rw [← hcount, countBelow_eq, shortFound]
  simp

theorem shortPointOK_spec {T : ShortTables} {v : ℕ} (h : shortPointOK T v = true)
    (hl : rd8 T.klev v ≠ 0) :
    (rd8 T.klev v = 1 → v = shortSeed) ∧
    (rd8 T.klev v ≠ 1 → rd32 T.kpar v < 2 ^ 24 ∧ rd8 T.klab v < 15 ∧
      rd8 T.klev (rd32 T.kpar v) + 1 = rd8 T.klev v ∧
      gimg (rd8 T.klab v) (rd32 T.kpar v) = v) := by
  unfold shortPointOK at h
  rw [ite_eq_right (by simpa using hl)] at h
  constructor
  · intro h1
    rw [ite_eq_left (by simpa using h1)] at h
    simpa using h
  · intro h1
    rw [ite_eq_right (by simpa using h1)] at h
    simpa [Bool.and_eq_true, and_assoc] using h

section Orbits

variable {G X : Type*} [Group G] [MulAction G X] {T : ShortTables} {dec : ℕ → X} {kGen : ℕ → G}

namespace ShortFacts

theorem mem_orbit (hF : ShortFacts T) (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p) :
    ∀ v < 2 ^ 24, rd8 T.klev v ≠ 0 →
      dec v ∈ MulAction.orbit (Subgroup.closure (kGen '' Set.Iio 15)) (dec shortSeed) := by
  intro v hv hl
  induction hlev : rd8 T.klev v using Nat.strong_induction_on generalizing v with
  | _ l ih =>
    obtain ⟨h1, hpar⟩ := shortPointOK_spec (hF.point v hv) hl
    by_cases hl1 : rd8 T.klev v = 1
    · rw [h1 hl1]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hp, hg, hlp, himg⟩ := hpar hl1
      have hpl : rd8 T.klev (rd32 T.kpar v) ≠ 0 := by omega
      have ihp := ih _ (by omega) _ hp hpl rfl
      rw [← himg, hk _ hg]
      exact smul_mem_orbit_closure (S := kGen '' Set.Iio 15) (Set.mem_image_of_mem kGen hg) ihp

theorem image_shortFound_subset_orbit (hF : ShortFacts T)
    (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p) :
    dec '' (shortFound T : Set ℕ) ⊆
      MulAction.orbit (Subgroup.closure (kGen '' Set.Iio 15)) (dec shortSeed) := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v ∈ shortFound T := hv
  simp only [shortFound, Finset.mem_filter, Finset.mem_range] at hv'
  exact hF.mem_orbit hk v hv'.1 hv'.2

theorem ncard_image_shortFound (hF : ShortFacts T)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) :
    (dec '' (shortFound T : Set ℕ)).ncard = shortCount := by
  have hinj : Set.InjOn dec (shortFound T : Set ℕ) := fun a ha b hb hab => by
    have ha' : a ∈ shortFound T := ha
    have hb' : b ∈ shortFound T := hb
    simp only [shortFound, Finset.mem_filter, Finset.mem_range] at ha' hb'
    exact hdec a b ha'.1 hb'.1 hab
  rw [hinj.ncard_image, Set.ncard_coe_finset, hF.card_found]

end ShortFacts

end Orbits

end CFSG.Monster.B.Short
