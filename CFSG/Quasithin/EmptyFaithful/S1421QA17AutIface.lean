module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17AutCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ2Aut

public section

namespace CFSG.Quasithin

namespace S1421QA17

namespace TXCode

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover.Models
  CFSG.EvenSporadicStandard.Fin76b.J2

@[expose] noncomputable def permC (c : ℕ) : Perm315 :=
  if c < 128 then (elt c : Perm315) else (elt (c - 128) : Perm315) * bOut

theorem permC_lt {c : ℕ} (h : c < 128) :
    permC c = (elt c : Perm315) := by
  simp [permC, h]

theorem permC_ge {c : ℕ} (h : 128 ≤ c) :
    permC c = (elt (c - 128) : Perm315) * bOut := by
  simp [permC, not_lt.2 h]

theorem permC_zero : permC 0 = 1 := by
  rw [permC_lt (by norm_num), elt_zero]
  rfl

theorem permC_mem_TX {c : ℕ} :
    permC c ∈ TX := by
  by_cases h : c < 128
  · rw [permC_lt h]
    exact S_le_TX (elt c).2
  · rw [permC_ge (not_lt.1 h)]
    refine Or.inr ?_
    rw [mul_assoc, bOut_mul_self, mul_one]
    exact (elt (c - 128)).2

theorem mulC_ll {c d : ℕ} (hc : c < 128) (hd : d < 128) : mulC c d = mulIdx c d := by
  have h1 : c % 128 = c := by omega
  have h2 : c / 128 = 0 := by omega
  have h3 : d % 128 = d := by omega
  have h4 : d / 128 = 0 := by omega
  simp [mulC, h1, h2, h3, h4]

theorem mulC_lg {c d : ℕ} (hc : c < 128) (hd : 128 ≤ d) (hd2 : d < 256) :
    mulC c d = mulIdx c (d - 128) + 128 := by
  have h1 : c % 128 = c := by omega
  have h2 : c / 128 = 0 := by omega
  have h3 : d % 128 = d - 128 := by omega
  have h4 : d / 128 = 1 := by omega
  simp [mulC, h1, h2, h3, h4]

theorem mulC_gl {c d : ℕ} (hc : 128 ≤ c) (hc2 : c < 256) (hd : d < 128) :
    mulC c d = mulIdx (c - 128) (betaIdx d) + 128 := by
  have h1 : c % 128 = c - 128 := by omega
  have h2 : c / 128 = 1 := by omega
  have h3 : d % 128 = d := by omega
  have h4 : d / 128 = 0 := by omega
  simp [mulC, h1, h2, h3, h4]

theorem mulC_gg {c d : ℕ} (hc : 128 ≤ c) (hc2 : c < 256) (hd : 128 ≤ d) (hd2 : d < 256) :
    mulC c d = mulIdx (c - 128) (betaIdx (d - 128)) := by
  have h1 : c % 128 = c - 128 := by omega
  have h2 : c / 128 = 1 := by omega
  have h3 : d % 128 = d - 128 := by omega
  have h4 : d / 128 = 1 := by omega
  simp [mulC, h1, h2, h3, h4]

theorem permC_mul {c d : ℕ}
    (hc : c < 256) (hd : d < 256) :
    mulC c d < 256 ∧ permC c * permC d = permC (mulC c d) := by
  by_cases h1 : c < 128 <;> by_cases h2 : d < 128
  · have hm := mulIdx_spec (a := c) h2
    rw [mulC_ll h1 h2]
    refine ⟨by omega, ?_⟩
    rw [permC_lt h1, permC_lt h2, permC_lt hm.1, coe_elt_mul c h2]
  · have hd' : d - 128 < 128 := by omega
    have hm := mulIdx_spec (a := c) hd'
    rw [mulC_lg h1 (not_lt.1 h2) hd]
    refine ⟨by omega, ?_⟩
    rw [permC_lt h1, permC_ge (not_lt.1 h2), permC_ge (by omega),
      show mulIdx c (d - 128) + 128 - 128 = mulIdx c (d - 128) by omega, ← mul_assoc,
      coe_elt_mul c hd']
  · have hc' : c - 128 < 128 := by omega
    have hb := betaIdx_lt h2
    have hm := mulIdx_spec (a := c - 128) hb
    rw [mulC_gl (not_lt.1 h1) hc h2]
    refine ⟨by omega, ?_⟩
    rw [permC_ge (not_lt.1 h1), permC_lt h2, permC_ge (by omega),
      show mulIdx (c - 128) (betaIdx d) + 128 - 128 = mulIdx (c - 128) (betaIdx d) by omega,
      mul_assoc, bOut_mul_elt h2, ← mul_assoc, coe_elt_mul (c - 128) hb]
  · have hc' : c - 128 < 128 := by omega
    have hd' : d - 128 < 128 := by omega
    have hb := betaIdx_lt hd'
    have hm := mulIdx_spec (a := c - 128) hb
    rw [mulC_gg (not_lt.1 h1) hc (not_lt.1 h2) hd]
    refine ⟨by omega, ?_⟩
    rw [permC_ge (not_lt.1 h1), permC_ge (not_lt.1 h2), permC_lt hm.1]
    calc (elt (c - 128) : Perm315) * bOut * ((elt (d - 128) : Perm315) * bOut)
        = (elt (c - 128) : Perm315) * (bOut * (elt (d - 128) : Perm315)) * bOut := by group
      _ = (elt (c - 128) : Perm315) * ((elt (betaIdx (d - 128)) : Perm315) * bOut) * bOut := by
          rw [bOut_mul_elt hd']
      _ = (elt (c - 128) : Perm315) * (elt (betaIdx (d - 128)) : Perm315) * (bOut * bOut) := by
          group
      _ = (elt (mulIdx (c - 128) (betaIdx (d - 128))) : Perm315) := by
          rw [bOut_mul_self, mul_one, coe_elt_mul (c - 128) hb]

theorem permC_injOn {c d : ℕ}
    (hc : c < 256) (hd : d < 256) (h : permC c = permC d) : c = d := by
  by_cases h1 : c < 128 <;> by_cases h2 : d < 128
  · rw [permC_lt h1, permC_lt h2] at h
    exact elt_injective h1 h2 (Subtype.ext h)
  · exfalso
    rw [permC_lt h1, permC_ge (not_lt.1 h2)] at h
    have e : bOut = ((elt (d - 128) : Perm315))⁻¹ * (elt c : Perm315) := by rw [h]; group
    exact bOut_not_mem_S (by
      rw [e]
      exact S.mul_mem (S.inv_mem (elt (d - 128)).2) (elt c).2)
  · exfalso
    rw [permC_ge (not_lt.1 h1), permC_lt h2] at h
    have e : bOut = ((elt (c - 128) : Perm315))⁻¹ * (elt d : Perm315) := by rw [← h]; group
    exact bOut_not_mem_S (by
      rw [e]
      exact S.mul_mem (S.inv_mem (elt (c - 128)).2) (elt d).2)
  · have h3 : (elt (c - 128) : Perm315) = elt (d - 128) := mul_right_cancel (by
      rw [permC_ge (not_lt.1 h1), permC_ge (not_lt.1 h2)] at h
      exact h)
    have := elt_injective (by omega) (by omega) (Subtype.ext h3)
    omega

theorem exists_permC
    {x : Perm315} (hx : x ∈ TX) :
    ∃ c, c < 256 ∧ x = permC c := by
  rcases exists_elt_TX hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact ⟨a, by omega, (permC_lt ha).symm⟩
  · refine ⟨a + 128, by omega, ?_⟩
    rw [permC_ge (by omega), Nat.add_sub_cancel]

theorem permC_not_mem_P
    {c : ℕ} (hc : 128 ≤ c) : permC c ∉ J2Cover.P := by
  rw [← P_eq_autP, permC_ge hc]
  intro h
  refine bOut_not_mem ?_
  have := P.mul_mem (P.inv_mem (S_le_P (elt (c - 128)).2)) h
  simpa using this

@[expose] noncomputable def eC
    (c : ℕ) : ↥J2Cover.R :=
  ⟨permC c, TX_le_R permC_mem_TX⟩

theorem coe_eC
    (c : ℕ) : ((eC c : ↥J2Cover.R) : Perm315) = permC c := rfl

theorem eC_mul
    {c d : ℕ} (hc : c < 256) (hd : d < 256) :
    eC c * eC d = eC (mulC c d) :=
  Subtype.ext (permC_mul hc hd).2

theorem mulC_lt {c d : ℕ}
    (hc : c < 256) (hd : d < 256) : mulC c d < 256 :=
  (permC_mul hc hd).1

theorem eC_injOn
    {c d : ℕ} (hc : c < 256) (hd : d < 256)
    (h : eC c = eC d) : c = d :=
  permC_injOn hc hd (congrArg Subtype.val h)

theorem eC_zero :
    eC 0 = 1 :=
  Subtype.ext (by rw [coe_eC, permC_zero]; rfl)

theorem eC_mem_T
    (c : ℕ) : eC c ∈ TX.subgroupOf J2Cover.R :=
  permC_mem_TX

theorem exists_eC
    {x : ↥J2Cover.R} (hx : x ∈ TX.subgroupOf J2Cover.R) :
    ∃ c, c < 256 ∧ x = eC c := by
  obtain ⟨c, hc, h⟩ := exists_permC hx
  exact ⟨c, hc, Subtype.ext h⟩

theorem lt_of_mem_centF {u c : ℕ} (h : c ∈ centF u) : c < 256 :=
  Finset.mem_range.1 (Finset.mem_filter.1 h).1

theorem mem_inf_centralizer_iff
    {u : ℕ} (hu : u < 256) {x : ↥J2Cover.R} :
    x ∈ TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC u} : Set ↥J2Cover.R) ↔
      ∃ c ∈ centF u, x = eC c := by
  constructor
  · rintro ⟨hxT, hxc⟩
    obtain ⟨c, hc, rfl⟩ := exists_eC hxT
    refine ⟨c, Finset.mem_filter.2 ⟨Finset.mem_range.2 hc, ?_⟩, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hxc
    rw [eC_mul hc hu, eC_mul hu hc] at h
    exact (eC_injOn (mulC_lt hc hu) (mulC_lt hu hc) h).symm
  · rintro ⟨c, hc, rfl⟩
    have hc256 := lt_of_mem_centF hc
    refine ⟨eC_mem_T c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [eC_mul hc256 hu, eC_mul hu hc256]
    exact congrArg eC (Finset.mem_filter.1 hc).2.symm

theorem natCard_eq_card_of_codes
    {H : Subgroup ↥J2Cover.R} {C : Finset ℕ}
    (hC : ∀ c ∈ C, c < 256) (hH : ∀ x : ↥J2Cover.R, x ∈ H ↔ ∃ c ∈ C, x = eC c) :
    Nat.card ↥H = C.card := by
  have hinj : Set.InjOn eC (C : Set ℕ) := fun a ha b hb h => eC_injOn (hC a ha) (hC b hb) h
  have hset : (H : Set ↥J2Cover.R) = eC '' (C : Set ℕ) := by
    ext x
    simp only [SetLike.mem_coe, hH, Set.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
  change Nat.card (H : Set ↥J2Cover.R) = _
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, Set.ncard_coe_finset]

@[expose] noncomputable def xElt
    {u : ℕ} (hu : u < 256) {a : ℕ} (h : a ∈ centF u) :
    ↥(TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC u} : Set ↥J2Cover.R)) :=
  ⟨eC a, (mem_inf_centralizer_iff hu).2 ⟨a, h, rfl⟩⟩

theorem exists_code_hom
    {u v : ℕ} (hu : u < 256) (hv : v < 256)
    (f : ↥(TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC u} : Set ↥J2Cover.R)) →*
      ↥(TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC v} : Set ↥J2Cover.R)))
    (hf : Function.Injective f) :
    ∃ g : ℕ → ℕ, (∀ a ∈ centF u, g a ∈ centF v) ∧ Set.InjOn g (centF u : Set ℕ) ∧
      (∀ a ∈ centF u, ∀ b ∈ centF u, mulC a b ∈ centF u) ∧
      (∀ a ∈ centF u, ∀ b ∈ centF u, g (mulC a b) = mulC (g a) (g b)) ∧
      0 ∈ centF u ∧ g 0 = 0 := by
  classical
  have hF : ∀ x : ↥(TX.subgroupOf J2Cover.R ⊓
      Subgroup.centralizer ({eC u} : Set ↥J2Cover.R)),
      ∃ c ∈ centF v, ((f x : ↥(TX.subgroupOf J2Cover.R ⊓
        Subgroup.centralizer ({eC v} : Set ↥J2Cover.R))) : ↥J2Cover.R) = eC c := fun x => by
    obtain ⟨c, hc, h⟩ := (mem_inf_centralizer_iff hv).1 (f x).2
    exact ⟨c, hc, h⟩
  choose F hFmem hFeq using hF
  let g : ℕ → ℕ := fun a => if h : a ∈ centF u then F (xElt hu h) else 0
  have hg : ∀ a (h : a ∈ centF u), g a = F (xElt hu h) := fun a h => by simp [g, h]
  have hgmem : ∀ a ∈ centF u, g a ∈ centF v := fun a h => by
    rw [hg a h]
    exact hFmem _
  have hgeq : ∀ a (h : a ∈ centF u), eC (g a) = ((f (xElt hu h) : ↥(TX.subgroupOf J2Cover.R ⊓
      Subgroup.centralizer ({eC v} : Set ↥J2Cover.R))) : ↥J2Cover.R) := fun a h => by
    rw [hg a h]
    exact (hFeq _).symm
  have hcl : ∀ a ∈ centF u, ∀ b ∈ centF u, mulC a b ∈ centF u := by
    intro a ha b hb
    have h1 : eC a * eC b ∈ TX.subgroupOf J2Cover.R ⊓
        Subgroup.centralizer ({eC u} : Set ↥J2Cover.R) :=
      Subgroup.mul_mem _ ((mem_inf_centralizer_iff hu).2 ⟨a, ha, rfl⟩)
        ((mem_inf_centralizer_iff hu).2 ⟨b, hb, rfl⟩)
    obtain ⟨c, hc, hce⟩ := (mem_inf_centralizer_iff hu).1 h1
    rw [eC_mul (lt_of_mem_centF ha) (lt_of_mem_centF hb)] at hce
    have := eC_injOn (mulC_lt (lt_of_mem_centF ha) (lt_of_mem_centF hb))
      (lt_of_mem_centF hc) hce
    rw [this]
    exact hc
  have h0 : 0 ∈ centF u := by
    have h1 : (1 : ↥J2Cover.R) ∈ TX.subgroupOf J2Cover.R ⊓
        Subgroup.centralizer ({eC u} : Set ↥J2Cover.R) := Subgroup.one_mem _
    obtain ⟨c, hc, hce⟩ := (mem_inf_centralizer_iff hu).1 h1
    rw [← eC_zero] at hce
    have := eC_injOn (by norm_num) (lt_of_mem_centF hc) hce
    rw [this]
    exact hc
  refine ⟨g, hgmem, ?_, hcl, ?_, h0, ?_⟩
  · intro a ha b hb hab
    have h1 := hgeq a ha
    have h2 := hgeq b hb
    have h3 : eC (g a) = eC (g b) := by
      show eC (g a) = eC (g b)
      rw [hab]
    have h4 : (f (xElt hu ha) : ↥(TX.subgroupOf J2Cover.R ⊓
        Subgroup.centralizer ({eC v} : Set ↥J2Cover.R))) = f (xElt hu hb) :=
      Subtype.ext (h1.symm.trans (h3.trans h2))
    have h5 := hf h4
    exact eC_injOn (lt_of_mem_centF ha) (lt_of_mem_centF hb) (congrArg Subtype.val h5)
  · intro a ha b hb
    have hab := hcl a ha b hb
    have e1 : xElt hu hab = xElt hu ha * xElt hu hb := Subtype.ext (by
      show eC (mulC a b) = eC a * eC b
      rw [eC_mul (lt_of_mem_centF ha) (lt_of_mem_centF hb)])
    have h1 := hgeq (mulC a b) hab
    rw [e1, map_mul, Subgroup.coe_mul, ← hgeq a ha, ← hgeq b hb,
      eC_mul (lt_of_mem_centF (hgmem a ha)) (lt_of_mem_centF (hgmem b hb))] at h1
    exact eC_injOn (lt_of_mem_centF (hgmem _ hab))
      (mulC_lt (lt_of_mem_centF (hgmem a ha)) (lt_of_mem_centF (hgmem b hb))) h1
  · have h1 := hgeq 0 h0
    have e0 : xElt hu h0 = 1 := Subtype.ext (by
      show eC 0 = 1
      exact eC_zero)
    rw [e0, map_one, Subgroup.coe_one, ← eC_zero] at h1
    exact eC_injOn (lt_of_mem_centF (hgmem 0 h0)) (by norm_num) h1

theorem jCode_lt : jCode < 256 := by decide

theorem eC_jCode_sq :
    eC jCode ^ 2 = 1 := by
  rw [sq, eC_mul jCode_lt jCode_lt]
  have h : mulC jCode jCode = 0 := sqC_jCode
  rw [h, eC_zero]

theorem eC_jCode_not_mem_P :
    eC jCode ∉ J2Cover.P.subgroupOf J2Cover.R :=
  fun h => permC_not_mem_P (c := jCode) (by decide) h

theorem natCard_T_inf_centralizer_j :
    Nat.card ↥(TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC jCode} : Set ↥J2Cover.R)) =
      32 := by
  rw [natCard_eq_card_of_codes (fun c hc => lt_of_mem_centF hc)
    (fun x => mem_inf_centralizer_iff jCode_lt)]
  exact bCard_eq

theorem w_clause :
    ∀ w ∈ TX.subgroupOf J2Cover.R, (∀ t ∈ TX.subgroupOf J2Cover.R, t * w = w * t) → w ≠ 1 →
      (∃ y ∈ TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC jCode} : Set ↥J2Cover.R),
        y ^ 2 = w) ∧
      ∀ x ∈ TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC jCode} : Set ↥J2Cover.R),
        x ^ 2 = 1 → (∃ y ∈ TX.subgroupOf J2Cover.R ⊓
          Subgroup.centralizer ({eC jCode} : Set ↥J2Cover.R), y ^ 2 = x) → x = 1 ∨ x = w := by
  intro w hwT hwc hw1
  have hw4 : w = eC 4 := by
    have hcen := (central_TX_iff (x := (w : Perm315)) hwT).1 (fun y hy => by
      have := hwc ⟨y, TX_le_R hy⟩ hy
      exact congrArg Subtype.val this)
    rcases hcen with h | h
    · exact absurd (Subtype.ext h) hw1
    · exact Subtype.ext (by rw [coe_eC, permC_lt (by norm_num)]; exact h)
  subst hw4
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy, hsq⟩ := exists_sq_four
    refine ⟨eC y, (mem_inf_centralizer_iff jCode_lt).2 ⟨y, hy, rfl⟩, ?_⟩
    have hy256 := lt_of_mem_centF hy
    rw [sq, eC_mul hy256 hy256]
    exact congrArg eC hsq
  · intro x hx hx2 ⟨y, hy, hyx⟩
    obtain ⟨a, ha, rfl⟩ := (mem_inf_centralizer_iff jCode_lt).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_inf_centralizer_iff jCode_lt).1 hy
    have ha256 := lt_of_mem_centF ha
    have hb256 := lt_of_mem_centF hb
    have h1 : sqC a = 0 := by
      rw [sq, eC_mul ha256 ha256, ← eC_zero] at hx2
      exact eC_injOn (mulC_lt ha256 ha256) (by norm_num) hx2
    have h2 : sqC b = a := by
      rw [sq, eC_mul hb256 hb256] at hyx
      exact eC_injOn (mulC_lt hb256 hb256) ha256 hyx
    rcases sq_cases a ha h1 ⟨b, hb, h2⟩ with h | h
    · left
      rw [h, eC_zero]
    · right
      rw [h]

theorem emb_clause :
    ∀ u ∈ TX.subgroupOf J2Cover.R ⊓ J2Cover.P.subgroupOf J2Cover.R, u ^ 2 = 1 → u ≠ 1 →
      ¬ ∃ f : ↥(TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({u} : Set ↥J2Cover.R)) →*
        ↥(TX.subgroupOf J2Cover.R ⊓ Subgroup.centralizer ({eC jCode} : Set ↥J2Cover.R)),
          Function.Injective f := by
  rintro u ⟨huT, huN⟩ hu2 hu1 ⟨f, hf⟩
  obtain ⟨a, ha, rfl⟩ := exists_eC huT
  have ha128 : a < 128 := by
    by_contra h
    exact permC_not_mem_P (not_lt.1 h) huN
  have ha0 : a ≠ 0 := fun h => hu1 (by rw [h, eC_zero])
  have hsq : sqC a = 0 := by
    rw [sq, eC_mul ha ha, ← eC_zero] at hu2
    exact eC_injOn (mulC_lt ha ha) (by norm_num) hu2
  have hcrit := crit_all a (Finset.mem_range.2 ha128) ha0 hsq
  obtain ⟨g, hgY, hinj, hcl, hhom, h0, hg0⟩ := exists_code_hom ha jCode_lt f hf
  obtain ⟨c1, c2, c3⟩ := code_hom_invariants (m := mulC) hgY hinj hcl hhom h0 hg0
  unfold CritF at hcrit
  rcases hcrit with h | h | h
  · exact absurd c1 (not_le.2 h)
  · exact absurd c2 (not_le.2 h)
  · exact absurd c3 (not_le.2 h)

end TXCode

end S1421QA17

end CFSG.Quasithin
