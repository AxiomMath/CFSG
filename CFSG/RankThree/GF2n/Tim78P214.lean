module

public import CFSG.RankThree.GF2n.Tim78P210Main
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem tightlyEmbedded_of_isTI {B : Subgroup G} (hB2 : IsPGroup 2 B) (hB1 : B ≠ ⊥)
    (hTI : IsTI B) : TightlyEmbedded B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun h hh => ?_⟩
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hB2
    rw [hk]
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq B (by simpa using hk)) hB1
    · exact Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩
  · rw [show rightConjugate B h = conjSubgroup h⁻¹ B by rw [← rightConjugate_inv_eq, inv_inv]]
    rcases hTI h⁻¹ with h0 | h0
    · rw [h0, Subgroup.card_bot]
      exact odd_one
    · exfalso
      apply hh
      have hle' : B ≤ conjSubgroup h⁻¹ B := h0.symm.le.trans inf_le_right
      have heq : conjSubgroup h⁻¹ B = B := (Subgroup.eq_of_le_of_card_ge hle'
        (card_conjSubgroup h⁻¹ B).le).symm
      have := conjSubgroup_eq_self_iff.mp heq
      simpa using (Subgroup.normalizer _).inv_mem this

omit [Finite G] in
theorem comm_conj {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (g : G) :
    ∀ x ∈ conjSubgroup g B, ∀ y ∈ conjSubgroup g B, x * y = y * x := by
  intro x hx y hy
  have h := hBc _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
  calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = y * x := by group

theorem frattini_ne_bot_of_sq_ne_one {B : Subgroup G} (hB2 : IsPGroup 2 B) {x : G} (hx : x ∈ B)
    (hx2 : x ^ 2 ≠ 1) : frattini ↥B ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hmem := CFSG.SectionRank.Ccomm.pow_mem_frattini hB2 ⟨x, hx⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hx2 (by simpa using congrArg Subtype.val hmem)

theorem commute_of_conj_le {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB2 : IsPGroup 2 B) (hTI : IsTI B) {x₀ : G} (hx₀ : x₀ ∈ B) (hx₀2 : x₀ ^ 2 ≠ 1)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hBS : B ≤ S) {g k : G} (hg : conjSubgroup g B ≤ S)
    (hk : conjSubgroup k B ≤ S) :
    ∀ a ∈ conjSubgroup g B, ∀ b ∈ conjSubgroup k B, a * b = b * a := by
  have hB1 : B ≠ ⊥ := fun h => hx₀2 (by
    rw [h, Subgroup.mem_bot] at hx₀
    rw [hx₀, one_pow])
  by_cases hgk : conjSubgroup g B = conjSubgroup k B
  · rw [← hgk]
    exact comm_conj hBc g
  have hs : Setup B ⊤ B S :=
    { tight := tightlyEmbedded_of_isTI hB2 hB1 hTI
      le_inf := le_inf le_top le_rfl
      sylow := fun R hR _ hBR => le_antisymm (hR.trans inf_le_right) hBR
      pGroup := hB2
      ne_bot := hB1
      S_le := le_top
      S_pGroup := hS
      le_S := hBS }
  exact hs.commutes_conjugatesIn (frattini_ne_bot_of_sq_ne_one hB2 hx₀ hx₀2) _
    ⟨g⁻¹, Subgroup.mem_top _, (rightConjugate_inv_eq B g).symm, hg⟩ _
    ⟨k⁻¹, Subgroup.mem_top _, (rightConjugate_inv_eq B k).symm, hk⟩ hgk

omit [Finite G] in
theorem exists_sq_ne_one {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBne : PartTwo.omegaOneSub B ≠ B) : ∃ x ∈ B, x ^ 2 ≠ 1 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hBne (le_antisymm (PartTwo.omegaOneSub_le B) fun x hx =>
    (mem_omegaOneSub_iff hBc).mpr ⟨hx, by rw [← sq]; exact h x hx⟩)

theorem sq_mem_normalizer {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB2 : IsPGroup 2 B) (hTI : IsTI B) {x₀ : G} (hx₀ : x₀ ∈ B) (hx₀2 : x₀ ^ 2 ≠ 1)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hBS : B ≤ S) (h : G)
    (h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup h B) ⊓ S)) {b : G} (hb : b ∈ B) :
    b * b ∈ Subgroup.normalizer (conjSubgroup h B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBhc := comm_conj hBc h
  have hTIh : IsTI (conjSubgroup h B) := isTI_conjSubgroup hTI h
  set V := PartTwo.omegaOneSub (conjSubgroup h B) ⊓ S with hV
  have hmemV : ∀ v, v ∈ V ↔ (v ∈ conjSubgroup h B ∧ v * v = 1) ∧ v ∈ S := fun v => by
    rw [hV, Subgroup.mem_inf, mem_omegaOneSub_iff hBhc]
  have hV1 : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨r, hrV⟩, hr1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
  have hr1 : r ≠ 1 := fun h' => hr1' (Subtype.ext h')
  obtain ⟨⟨hrB, hrr⟩, hrS⟩ := (hmemV r).mp hrV
  obtain ⟨s, hsV, hs1, hsr⟩ : ∃ s ∈ V, s ≠ 1 ∧ s ≠ r := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hle : V ≤ Subgroup.zpowers r := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]
        exact Subgroup.one_mem _
      · by_cases hvr : v = r
        · rw [hvr]
          exact Subgroup.mem_zpowers r
        · exact absurd hvr (hcon v hv hv1)
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hrr) hr1] at hcard
    omega
  obtain ⟨⟨hsB, hss⟩, hsS⟩ := (hmemV s).mp hsV
  have hrs : r * s = s * r := hBhc r hrB s hsB
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  obtain ⟨q, hq⟩ : ∃ q : G, q = r * s := ⟨_, rfl⟩
  have hqB : q ∈ conjSubgroup h B := by
    rw [hq]
    exact (conjSubgroup h B).mul_mem hrB hsB
  have hqS : q ∈ S := by
    rw [hq]
    exact S.mul_mem hrS hsS
  have hq1 : q ≠ 1 := fun h' => hsr (by
    rw [hq] at h'
    rw [eq_inv_of_mul_eq_one_right h', hrinv])
  have hqq : q * q = 1 := by
    rw [hq, show r * s * (r * s) = r * (s * r) * s by group, ← hrs,
      show r * (r * s) * s = (r * r) * (s * s) by group, hrr, hss, one_mul]
  have hconjS : ∀ x ∈ S, conjSubgroup x B ≤ S := fun x hx y hy => by
    rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group]
    exact S.mul_mem (S.mul_mem hx (hBS (mem_conjSubgroup.mp hy))) (S.inv_mem hx)
  have hcomm : ∀ x ∈ S, ∀ x' ∈ S, ∀ c ∈ conjSubgroup x B, ∀ c' ∈ conjSubgroup x' B,
      c * c' = c' * c := fun x hx x' hx' =>
    commute_of_conj_le hBc hB2 hTI hx₀ hx₀2 hS hBS (hconjS x hx) (hconjS x' hx')
  have hmemc : ∀ x : G, x * b * x⁻¹ ∈ conjSubgroup x B := fun x => by
    rw [mem_conjSubgroup, show x⁻¹ * (x * b * x⁻¹) * x = b by group]
    exact hb
  have hb1 : b ∈ conjSubgroup 1 B := by
    rw [conjSubgroup_one]
    exact hb
  have c_r : b * (r * b * r⁻¹) = (r * b * r⁻¹) * b := hcomm 1 S.one_mem r hrS b hb1 _ (hmemc r)
  have c_s : b * (s * b * s⁻¹) = (s * b * s⁻¹) * b := hcomm 1 S.one_mem s hsS b hb1 _ (hmemc s)
  have c_q : b * (q * b * q⁻¹) = (q * b * q⁻¹) * b := hcomm 1 S.one_mem q hqS b hb1 _ (hmemc q)
  have c_sq : (s * b * s⁻¹) * (q * b * q⁻¹) = (q * b * q⁻¹) * (s * b * s⁻¹) :=
    hcomm s hsS q hqS _ (hmemc s) _ (hmemc q)
  have hd : ∀ x : G, x * x = 1 → b * (x * b * x⁻¹) = (x * b * x⁻¹) * b →
      (b * (x * b * x⁻¹)) * x = x * (b * (x * b * x⁻¹)) := by
    intro x hxx hc
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    calc (b * (x * b * x⁻¹)) * x = ((x * b * x⁻¹) * b) * x := by rw [hc]
      _ = x * (b * (x * b * x⁻¹)) := by rw [hxinv]; group
  have hdr := Tim77.mem_normalizer_of_commute_of_isTI hTIh hrB hr1 (hd r hrr c_r)
  have hds := Tim77.mem_normalizer_of_commute_of_isTI hTIh hsB hs1 (hd s hss c_s)
  have hdq := Tim77.mem_normalizer_of_commute_of_isTI hTIh hqB hq1 (hd q hqq c_q)
  have e2 : r * (r * b * r⁻¹) * r⁻¹ = b := by
    rw [show r * (r * b * r⁻¹) * r⁻¹ = (r * r) * b * (r * r)⁻¹ by group, hrr]
    group
  have e3 : r * (s * b * s⁻¹) * r⁻¹ = q * b * q⁻¹ := by
    rw [hq]
    group
  have e4 : r * (q * b * q⁻¹) * r⁻¹ = s * b * s⁻¹ := by
    rw [hq, show r * (r * s * b * (r * s)⁻¹) * r⁻¹ = (r * r) * s * b * s⁻¹ * (r * r)⁻¹ by group,
      hrr]
    group
  have ht : r * (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹)) * r⁻¹ =
      b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹) := by
    calc r * (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹)) * r⁻¹ =
        (r * b * r⁻¹) * (r * (r * b * r⁻¹) * r⁻¹) * (r * (s * b * s⁻¹) * r⁻¹) *
          (r * (q * b * q⁻¹) * r⁻¹) := by group
      _ = (r * b * r⁻¹) * b * ((q * b * q⁻¹) * (s * b * s⁻¹)) := by rw [e2, e3, e4]; group
      _ = (b * (r * b * r⁻¹)) * ((s * b * s⁻¹) * (q * b * q⁻¹)) := by rw [← c_r, ← c_sq]
      _ = b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹) := by group
  have htN := Tim77.mem_normalizer_of_commute_of_isTI hTIh hrB hr1 (c := b * (r * b * r⁻¹) *
    (s * b * s⁻¹) * (q * b * q⁻¹)) (by
      calc b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹) * r =
          r * (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹)) * r⁻¹ * r := by rw [ht]
        _ = r * (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹)) := by group)
  have hprod : (b * (r * b * r⁻¹)) * (b * (s * b * s⁻¹)) * (b * (q * b * q⁻¹)) =
      b * b * (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹)) := by
    calc (b * (r * b * r⁻¹)) * (b * (s * b * s⁻¹)) * (b * (q * b * q⁻¹)) =
        b * ((r * b * r⁻¹) * b) * (s * b * s⁻¹) * b * (q * b * q⁻¹) := by group
      _ = b * (b * (r * b * r⁻¹)) * ((s * b * s⁻¹) * b) * (q * b * q⁻¹) := by
          rw [← c_r]
          group
      _ = b * (b * (r * b * r⁻¹)) * (b * (s * b * s⁻¹)) * (q * b * q⁻¹) := by rw [← c_s]
      _ = b * b * ((r * b * r⁻¹) * b) * (s * b * s⁻¹) * (q * b * q⁻¹) := by group
      _ = b * b * (b * (r * b * r⁻¹)) * (s * b * s⁻¹) * (q * b * q⁻¹) := by rw [← c_r]
      _ = b * b * (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹)) := by group
  have hbb : b * b = (b * (r * b * r⁻¹)) * (b * (s * b * s⁻¹)) * (b * (q * b * q⁻¹)) *
      (b * (r * b * r⁻¹) * (s * b * s⁻¹) * (q * b * q⁻¹))⁻¹ := by
    rw [hprod]
    group
  rw [hbb]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hdr hds) hdq)
    (Subgroup.inv_mem _ htN)

theorem tim78_2_14_b (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB2 : IsPGroup 2 B)
    (hTI : IsTI B) (hBne : PartTwo.omegaOneSub B ≠ B) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hBS : B ≤ S) (h : G) (h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup h B) ⊓ S)) :
    ∀ a ∈ PartTwo.omegaOneSub B, ∀ b ∈ PartTwo.omegaOneSub (conjSubgroup h B),
      a * b = b * a := by
  obtain ⟨x₀, hx₀, hx₀2⟩ := exists_sq_ne_one hBc hBne
  have hN : B ⊓ Subgroup.normalizer (conjSubgroup h B : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : x₀ * x₀ ∈ B ⊓ Subgroup.normalizer (conjSubgroup h B : Set G) :=
      Subgroup.mem_inf.mpr ⟨B.mul_mem hx₀ hx₀,
        sq_mem_normalizer hBc hB2 hTI hx₀ hx₀2 hS hBS h h4 hx₀⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx₀2 (by rw [sq]; exact hmem)
  have T : Setup210 B (conjSubgroup h B) :=
    { comm := hBc
      two := hB2
      exp_ne := ⟨x₀, hx₀, hx₀2⟩
      ti := hTI
      conj := ⟨h, rfl⟩
      ne_bot := hN }
  exact (tim78_2_10_a hCen hU T).1

end CFSG.RankThree.GF2n.Tim78
