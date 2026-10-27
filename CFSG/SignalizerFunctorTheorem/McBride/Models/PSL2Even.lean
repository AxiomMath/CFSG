module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
import CFSG.SignalizerFunctorTheorem.NearModels.Main
import CFSG.Walter.PSL2Facts.Even
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Dickson
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.S3
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Setup

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

open PSL2Even CFSG.SignalizerFunctorTheorem.NearModels

theorem exists_aut_psl2Even {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p))) :
    ∃ f : MulAut PSL(2, GaloisField 2 p), orderOf f = p :=
  PSL2Even.exists_aut hp

theorem frame_psl2Even
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) : Frame p 3 f := by
  have hodd := odd_of_coprime hp hcop
  have hY2 := hY2_of_charTwo (p := p)
  obtain ⟨c, t, h⟩ := exists_S3Data_of_coprime hp hcop f hf
  have hnc : ¬ Commute c t := not_commute_of_orderOf_three hY2 h.order_c h.order_t
  have hcnc : ∃ a ∈ signalizerFixedSubgroup f, ∃ b ∈ signalizerFixedSubgroup f, a * b ≠ b * a :=
    ⟨c, h.c_mem, t, h.t_mem, hnc⟩
  refine
    { prime := hp
      prime_ℓ := Nat.prime_three
      ord := hf
      coprime := hcop
      simple := isSimpleGroup_of_prime hp
      nonabelian := ⟨c, t, hnc⟩
      fixed_solvable :=
        nearSimpleModel_fixedSubgroup_solvable hp (Or.inl ⟨MulEquiv.refl _⟩) hcop f hf
      C0_ne_bot := ?_
      C0_pgroup := ?_
      C0_comm := ?_
      C0_sylow := fun Q hQ hle => h.sylow_eq (not_nine_dvd_card_of_coprime hp hcop) hQ hle
      C0_ne := ?_
      C1_ne := h.fixedCore1_ne
      minimal := ?_
      centralizer_comm := ?_
      fpf := ?_
      normalizer_le := ?_
      overgroup := ?_ }
  · rw [h.fixedFitting_eq]
    intro hbot
    have := h.card_zpowers
    rw [hbot, Subgroup.card_bot] at this
    omega
  · rw [h.fixedFitting_eq]
    exact IsPGroup.of_card (n := 1) (by rw [h.card_zpowers]; norm_num)
  · rw [h.fixedFitting_eq]
    infer_instance
  · rw [h.fixedFitting_eq]
    intro heq
    have := h.card_zpowers
    rw [heq, h.card] at this
    omega
  · intro N hNC hN hbot
    rw [h.fixedFitting_eq]
    exact h.zpowers_le_of_normal hNC hN hbot
  · rw [h.fixedFitting_eq]
    exact h.isMulCommutative_centralizer hY2
  · intro v hv hvP z hz hvz
    rw [h.fixedFitting_eq] at hvP hz
    exact h.eq_one_of_commute hY2 hv hvP hz hvz
  · intro x hx
    rw [fixedNormalizer, h.fixedFitting_eq] at hx
    rw [h.fixedFitting_eq]
    exact h.exists_normalizer_decomp hx
  · intro H hCH hH
    rw [fixedNormalizer, h.fixedFitting_eq]
    apply le_normalizer_zpowers
    rcases overgroup_cases hp hodd h.card hcnc hCH hH with rfl | ⟨z, -, -, ⟨e⟩⟩
    · exact fun g hg => h.conj_mem_zpowers hg
    · exact dihedral_conj_mem e (hCH h.c_mem) h.order_c

theorem isCoatom_fixedNormalizer_psl2Even
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) :
    IsCoatom (fixedNormalizer f) := by
  have hF := frame_psl2Even hp hcop f hf
  have hMtop : fixedNormalizer f ≠ ⊤ := by
    intro htop
    have hnorm : (fixedFitting f).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hF.simple.eq_bot_or_eq_top_of_normal (fixedFitting f) with h1 | h1
    · exact hF.C0_ne_bot h1
    · exact hF.C0_ne (le_antisymm (fixedFitting_le f) (h1 ▸ le_top))
  refine ⟨hMtop, fun b hb => ?_⟩
  by_contra hbtop
  exact not_le_of_gt hb (hF.overgroup b ((fixed_le_fixedNormalizer f).trans hb.le) hbtop)

theorem itemC_psl2Even {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) : ItemC p f := by
  have hY2 := hY2_of_charTwo (p := p)
  obtain ⟨c, t, h⟩ := exists_S3Data_of_coprime hp hcop f hf
  refine isPGroup_of_coprime_eq_one hp fun g hgcop => ?_
  have hfix : ∀ y ∈ signalizerFixedSubgroup f, (g : MulAut PSL(2, GaloisField 2 p)) y = y :=
    fun y hy => (mem_fixingSubgroup_iff _).mp g.2 y hy
  have hgcop' : Nat.Coprime p (orderOf (g : MulAut PSL(2, GaloisField 2 p))) := by
    rwa [Subgroup.orderOf_coe]
  obtain ⟨x, hx⟩ := exists_conj_of_coprime_orderOf hp _ hgcop'
  have hxc : x * c * x⁻¹ = c := by
    have := hfix c h.c_mem
    rwa [hx, MulAut.conj_apply] at this
  have hxt : x * t * x⁻¹ = t := by
    have := hfix t h.t_mem
    rwa [hx, MulAut.conj_apply] at this
  have hcx : Commute c x := by
    show c * x = x * c
    calc c * x = (x * c * x⁻¹) * x := by rw [hxc]
      _ = x * c := by group
  have hxt' : Commute x t := by
    show x * t = t * x
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [hxt]
  have hx1 : x = 1 := eq_one_of_commute_of_odd hY2 h.order_t
    (odd_orderOf_of_commute hY2 h.order_c hcx) hxt'
  apply Subtype.ext
  rw [hx, hx1, map_one]
  rfl

theorem itemG_psl2Even
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) : ItemG p f := by
  intro g hg hM _
  obtain ⟨x, rfl⟩ := exists_conj_of_coprime_orderOf hp g hg
  refine ⟨x, ?_, rfl⟩
  have hxN : x ∈ Subgroup.normalizer (fixedNormalizer f : Set PSL(2, GaloisField 2 p)) :=
    mem_normalizer_of_forall_conj_mem fun m hm => by
      simpa [MulAut.conj_apply] using hM m hm
  have hF := frame_psl2Even hp hcop f hf
  have hbot : fixedNormalizer f ≠ ⊥ := fun h0 =>
    hF.C0_ne_bot (le_bot_iff.mp (h0 ▸ Subgroup.le_normalizer))
  rwa [normalizer_eq_of_isCoatom hF.simple (isCoatom_fixedNormalizer_psl2Even hp hcop f hf)
    hbot] at hxN

theorem itemO_psl2Even
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) : ItemO f := by
  have hodd := odd_of_coprime hp hcop
  have hY2 := hY2_of_charTwo (p := p)
  obtain ⟨c, t, h⟩ := exists_S3Data_of_coprime hp hcop f hf
  have hcnc : ∃ a ∈ signalizerFixedSubgroup f, ∃ b ∈ signalizerFixedSubgroup f, a * b ≠ b * a :=
    ⟨c, h.c_mem, t, h.t_mem, not_commute_of_orderOf_three hY2 h.order_c h.order_t⟩
  have hMcard : Nat.card (fixedNormalizer f) ∣ 2 * (2 ^ p + 1) :=
    card_dvd_of_overgroup hp hodd h.card hcnc (fixed_le_fixedNormalizer f)
      (isCoatom_fixedNormalizer_psl2Even hp hcop f hf).1
  have hodd1 := odd_two_pow_sub_one hp.pos
  refine ⟨?_, ?_⟩
  · have h4 : 4 ≤ 2 ^ p := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ p - 1 ≠ 1 by omega)
    refine ⟨r, hr, ?_, fun hrM => ?_⟩
    · rw [CFSG.Walter.psl2_even_card hp.ne_zero,
        show (2 ^ p) ^ 2 - 1 = (2 ^ p + 1) * (2 ^ p - 1) by rw [← Nat.sq_sub_sq, one_pow]]
      exact (hrd.mul_left _).mul_left _
    · have h2 := hrM.trans hMcard
      rcases (Nat.Prime.dvd_mul hr).mp h2 with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
        subst this
        obtain ⟨k, hk⟩ := hodd1
        omega
      · have h3 : r ∣ (2 ^ p + 1) - (2 ^ p - 1) := Nat.dvd_sub h2 hrd
        rw [show (2 ^ p + 1) - (2 ^ p - 1) = 2 by omega] at h3
        have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
        subst this
        obtain ⟨k, hk⟩ := hodd1
        omega
  · intro r hr _ hrM R
    have h2M : 2 ∣ Nat.card (fixedNormalizer f) := by
      have := Subgroup.orderOf_dvd_natCard (fixedNormalizer f)
        (fixed_le_fixedNormalizer f h.t_mem)
      rwa [h.order_t] at this
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact hrM h2M
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
    refine isMulCommutative_of_odd_card hp hodd (R : Subgroup PSL(2, GaloisField 2 p)) ?_
    rw [hk]
    exact (hr.odd_of_ne_two hr2).pow

theorem fixedCore1_psl2Even {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) :
    fixedCore1 f = signalizerFixedSubgroup f := by
  obtain ⟨c, t, h⟩ := exists_S3Data_of_coprime hp hcop f hf
  refine le_antisymm (fun x hx => hx.1) fun x hx => ⟨hx, fun y hy => ?_⟩
  rw [h.fixedFitting_eq]
  exact h.commutator_mem hx hy

theorem outer_perfect_psl2Even {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p))) :
    ∀ P : Subgroup (MulAut PSL(2, GaloisField 2 p)), Group.IsPerfect P →
      P ≤ (MulAut.conj : PSL(2, GaloisField 2 p) →* MulAut PSL(2, GaloisField 2 p)).range := by
  intro P hP
  have : Fact p.Prime := ⟨hp⟩
  have hnorm : ((MulAut.conj : PSL(2, GaloisField 2 p) →*
      MulAut PSL(2, GaloisField 2 p)).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set Inn := (MulAut.conj : PSL(2, GaloisField 2 p) →* MulAut PSL(2, GaloisField 2 p)).range
  have hP₁ : (Inn.subgroupOf P).Normal := inferInstance
  have hQp : IsPGroup p (P ⧸ Inn.subgroupOf P) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨a, ha⟩ := exists_pow_mem_range_conj hp (g : MulAut PSL(2, GaloisField 2 p))
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ha
  have hnil : Group.IsNilpotent (P ⧸ Inn.subgroupOf P) := hQp.isNilpotent
  have hsub : Subsingleton (P ⧸ Inn.subgroupOf P) := by
    by_contra h
    have : Nontrivial (P ⧸ Inn.subgroupOf P) := not_subsingleton_iff_nontrivial.mp h
    have : Group.IsPerfect (P ⧸ Inn.subgroupOf P) := inferInstance
    exact Group.IsPerfect.not_isNilpotent _ hnil
  intro g hg
  have h1 : (QuotientGroup.mk ⟨g, hg⟩ : P ⧸ Inn.subgroupOf P) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem outer_coprime_pow_six_psl2Even {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p))) :
    ∀ g : MulAut PSL(2, GaloisField 2 p), Nat.Coprime p (orderOf g) →
      g ^ 6 ∈ (MulAut.conj : PSL(2, GaloisField 2 p) →*
        MulAut PSL(2, GaloisField 2 p)).range := by
  intro g hg
  obtain ⟨x, rfl⟩ := exists_conj_of_coprime_orderOf hp g hg
  exact ⟨x ^ 6, by rw [map_pow]⟩

end CFSG.SignalizerFunctorTheorem.McBride
