module

public import CFSG.RankThree.GF2n.Basic
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
import CFSG.LocalAnalysis.SignalizerFunctor.FrattiniAutomorphismKernel

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_critical {M : Subgroup G} :
    ∃ S : Subgroup G, S ≤ inSubgroup (pCore 2) M ∧
      M ≤ Subgroup.normalizer (S : Set G) ∧
      inSubgroup frattini S ≤ S ⊓ Subgroup.centralizer (S : Set G) ∧
      inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (S : Set G) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  obtain ⟨⟨S', hchar, hΦ, -, hcen⟩, -⟩ :=
    CFSG.SectionRank.Ccomm.thompson_critical_subgroup (P := Q) (p := 2) hQ2
  set S := S'.map Q.subtype with hSdef
  have hS2 : IsPGroup 2 S := hQ2.to_le (Subgroup.map_subtype_le _)
  have hZ : ∀ w ∈ S' ⊓ Subgroup.centralizer (S' : Set Q), (w : G) ∈ S ⊓
      Subgroup.centralizer (S : Set G) := by
    intro w hw
    refine ⟨Subgroup.mem_map_of_mem _ hw.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hw.2 v hv)
  refine ⟨S, Subgroup.map_subtype_le _, fun m hm =>
    mem_normalizer_map_subtype_of_characteristic (hMQ hm) S', ?_, ?_⟩
  · refine inSubgroup_frattini_le_of_sq hS2 (fun s hs => ?_) (fun a ha b hb => ?_)
    · obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
      have : Fact (IsPGroup 2 S') := ⟨hQ2.to_subgroup S'⟩
      have h1 : (⟨s', hs'⟩ : S') ^ 2 ∈ frattini S' := pth_power_mem_frattini_of_isPGroup (p := 2) _
      have h2 := hΦ (Subgroup.mem_map_of_mem S'.subtype h1)
      have := hZ _ h2
      simpa using this
    · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have : Fact (IsPGroup 2 S') := ⟨hQ2.to_subgroup S'⟩
      have h1 : ⁅(⟨a', ha'⟩ : S'), ⟨b', hb'⟩⁆ ∈ frattini S' :=
        commutator_le_frattini_of_isPGroup (p := 2)
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      have h2 := hΦ (Subgroup.mem_map_of_mem S'.subtype h1)
      have := hZ _ h2
      simpa [commutatorElement_def] using this
  · rintro q ⟨hqQ, hqc⟩
    have hq' : (⟨q, hqQ⟩ : Q) ∈ Subgroup.centralizer (S' : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hqc _ (Subgroup.mem_map_of_mem _ hv))
    rw [hcen] at hq'
    exact Subgroup.mem_map_of_mem Q.subtype hq'.1


theorem commute_of_trivial_on_frattini {S : Subgroup G} (hS2 : IsPGroup 2 S) {c : G}
    (hcS : c ∈ Subgroup.normalizer (S : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hcr : orderOf c = r)
    (htriv : ∀ k : ℤ, ∀ s ∈ S, s⁻¹ * (c ^ k * s * (c ^ k)⁻¹) ∈ inSubgroup frattini S) :
    ∀ s ∈ S, c * s = s * c := by
  set A := Subgroup.zpowers c with hAdef
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := Subgroup.zpowers_le.mpr hcS
  set φ : A →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hAS) with hφdef
  have hφ : ∀ (a : A) (s : S), ((φ a s : S) : G) = (a : G) * s * (a : G)⁻¹ := fun _ _ => rfl
  have : Fact r.Prime := ⟨hr⟩
  have hA : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcr, pow_one])
  have hle : φ.range ≤ CFSG.SignalizerFunctor.Helpers.frattiniAutomorphismKernel S := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩ s
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 := htriv k _ s.2
    obtain ⟨w, hw, hws⟩ := Subgroup.mem_map.mp h1
    have : s⁻¹ * φ ⟨c ^ k, ha⟩ s = w := by
      apply Subtype.ext
      rw [show ((w : S) : G) = S.subtype w from rfl, hws]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
    rw [this]
    exact hw
  have hbot := CFSG.SignalizerFunctor.Helpers.frattini_automorphism_kernel_coprime_subgroup_trivial
    2 r Nat.prime_two hr (Ne.symm hr2) hS2 φ.range hle
    (hA.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
  intro s hs
  have hc : φ ⟨c, Subgroup.mem_zpowers c⟩ = 1 := by
    have : φ ⟨c, Subgroup.mem_zpowers c⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have h1 := congrArg (fun ψ : MulAut S => ((ψ ⟨s, hs⟩ : S) : G)) hc
  simp only [hφ, MulAut.one_apply] at h1
  calc c * s = c * s * c⁻¹ * c := by group
    _ = s * c := by rw [h1]

theorem tim78_2_3 {M : Subgroup G} (hF : generalizedFitting M = pCore 2 M) {y : G} (hyM : y ∈ M)
    (hy : ∃ k : ℕ, y ^ 2 ^ k = 1)
    (hC : inSubgroup (pCore 2) M ⊓ Subgroup.centralizer ({y} : Set G) =
      inSubgroup (pCore 2) M ⊓ Subgroup.centralizer ({y ^ 2} : Set G)) :
    y ^ 2 ∈ inSubgroup (pCore 2) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hCQ := inf_centralizer_le_of_generalizedFitting_eq hF
  obtain ⟨S, hSQ, hMS, hΦS, hcenS⟩ := exists_critical (M := M)
  have hS2 : IsPGroup 2 S := hQ2.to_le hSQ
  have hΦN : ∀ m ∈ M, m ∈ Subgroup.normalizer ((inSubgroup frattini S : Subgroup G) : Set G) :=
    fun m hm => mem_normalizer_inSubgroup_frattini (hMS hm)
  have hCS : S ⊓ Subgroup.centralizer ({y} : Set G) =
      S ⊓ Subgroup.centralizer ({y ^ 2} : Set G) := by
    ext z
    have h1 : z ∈ Q ⊓ Subgroup.centralizer ({y} : Set G) ↔
        z ∈ Q ⊓ Subgroup.centralizer ({y ^ 2} : Set G) := by rw [hC]
    have h2 := @hSQ z
    simp only [Subgroup.mem_inf] at h1 ⊢
    tauto
  have hβ := (tim78_2_2 hS2 hΦS (hMS hyM) hy hCS).2
  let T : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ∀ s ∈ S, s⁻¹ * (m * s * m⁻¹) ∈ inSubgroup frattini S}
      one_mem' := by
        refine ⟨M.one_mem, fun s _ => ?_⟩
        rw [one_mul, inv_one, mul_one, inv_mul_cancel]
        exact Subgroup.one_mem _
      mul_mem' := by
        rintro m₁ m₂ ⟨hm₁, h₁⟩ ⟨hm₂, h₂⟩
        refine ⟨M.mul_mem hm₁ hm₂, fun s hs => ?_⟩
        have hs' := conj_mem_of_mem_normalizer (hMS hm₂) hs
        have e : s⁻¹ * (m₁ * m₂ * s * (m₁ * m₂)⁻¹) =
            (s⁻¹ * (m₁ * s * m₁⁻¹)) * (m₁ * (s⁻¹ * (m₂ * s * m₂⁻¹)) * m₁⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (h₁ s hs)
          ((Subgroup.mem_normalizer_iff.mp (hΦN m₁ hm₁) _).mp (h₂ s hs))
      inv_mem' := by
        rintro m ⟨hm, h⟩
        refine ⟨M.inv_mem hm, fun s hs => ?_⟩
        have hs' : m⁻¹ * s * m ∈ S := by
          have := conj_mem_of_mem_normalizer (hMS (M.inv_mem hm)) hs
          simpa using this
        have h1 := h _ hs'
        have e : s⁻¹ * (m⁻¹ * s * m⁻¹⁻¹) = ((m⁻¹ * s * m)⁻¹ * (m * (m⁻¹ * s * m) * m⁻¹))⁻¹ := by
          group
        rw [e]
        exact Subgroup.inv_mem _ h1 }
  have hTM : T ≤ M := fun m hm => hm.1
  have hMT : M ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun m hm => ⟨M.mul_mem (M.mul_mem hg hm.1)
      (M.inv_mem hg), fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g ∈ S := by
      have := conj_mem_of_mem_normalizer (hMS (M.inv_mem hg)) hs
      simpa using this
    have h1 := hm.2 _ hs'
    have e : s⁻¹ * (g * m * g⁻¹ * s * (g * m * g⁻¹)⁻¹) =
        g * ((g⁻¹ * s * g)⁻¹ * (m * (g⁻¹ * s * g) * m⁻¹)) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hΦN g hg) _).mp h1
  have hyT : y ^ 2 ∈ T := ⟨M.pow_mem hyM 2, hβ⟩
  have hodd : ∀ c ∈ T, ∀ r : ℕ, r.Prime → r ≠ 2 → orderOf c = r → False := by
    intro c hcT r hr hr2 hcr
    have hcM := hTM hcT
    have hcS : ∀ s ∈ S, c * s = s * c :=
      commute_of_trivial_on_frattini hS2 (hMS hcM) hr hr2 hcr fun k s hs =>
        (T.zpow_mem hcT k).2 s hs
    have hcQ := commute_of_thompson_A_times_B hQ2 hS2 (hMQ hcM)
      (fun s hs => hMQ (hQM (hSQ hs))) (by rw [hcr]; exact hr.odd_of_ne_two hr2) hcS
      (fun q hq hqS => by
        have : q ∈ S := hcenS ⟨hq, Subgroup.mem_centralizer_iff.mpr fun s hs => (hqS s hs).symm⟩
        exact hcS q this)
    have hcQ' : c ∈ Q := hCQ ⟨hcM, Subgroup.mem_centralizer_iff.mpr fun q hq => (hcQ q hq).symm⟩
    have := eq_one_of_odd_of_isPGroup hQ2 hcQ' (by rw [hcr]; exact hr.odd_of_ne_two hr2)
    rw [this, orderOf_one] at hcr
    exact hr.one_lt.ne' hcr.symm
  have hT2 : IsPGroup 2 T := by
    intro t
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (t : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    set u := (t : G) ^ 2 ^ a with hu
    have huT : u ∈ T := T.pow_mem t.2 _
    by_contra hu1
    have hne : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hrd)
    have hpos : orderOf u ≠ 0 := (orderOf_pos u).ne'
    exact hodd _ (T.pow_mem huT _) r hr hr2 (orderOf_pow_orderOf_div hpos hrd)
  exact le_inSubgroup_pCore hTM hMT hT2 hyT

end CFSG.RankThree.GF2n.Tim78
