module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFourA
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77 Subgroup
open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {p m : ℕ} {π : Γ →* Equiv.Perm (ZMod p)} {D : Set Γ}

private lemma nine3_B_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hp.two_le)

private lemma nine3_B_zmodRefl_sq (c : ZMod p) :
    zmodRefl p c * zmodRefl p c = 1 := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.Perm.coe_one, id_eq]
  ring

private lemma nine3_B_zmodRefl_inv (c : ZMod p) :
    (zmodRefl p c)⁻¹ = zmodRefl p c :=
  inv_eq_of_mul_eq_one_right (nine3_B_zmodRefl_sq c)

private lemma nine3_B_zmodRefl_conj (c a : ZMod p) :
    zmodRefl p c * zmodRefl p a * zmodRefl p c = zmodRefl p (2 * c - a) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply]
  ring

private lemma nine3_B_zmodRefl_ne_one (hp : p.Prime) (hp2 : p ≠ 2) (c : ZMod p) :
    zmodRefl p c ≠ 1 := by
  intro h
  have h0 : (2 : ZMod p) * c = 0 := by
    have hc := congrArg (fun e : Equiv.Perm (ZMod p) => e 0) h
    simpa [zmodRefl, Equiv.subLeft] using hc
  have h1 : (2 : ZMod p) * c = 2 := by
    have hc := congrArg (fun e : Equiv.Perm (ZMod p) => e 1) h
    have h1' : (2 : ZMod p) * c - 1 = 1 := by simpa [zmodRefl, Equiv.subLeft] using hc
    calc (2 : ZMod p) * c = ((2 : ZMod p) * c - 1) + 1 := (sub_add_cancel _ _).symm
      _ = 1 + 1 := by rw [h1']
      _ = 2 := by norm_num
  exact nine3_B_two_ne_zero hp hp2 (by rw [← h1, h0])

private lemma nine3_B_zmodRefl_mul_ne_one (hp : p.Prime) (hp2 : p ≠ 2) {r s : ZMod p}
    (hrs : r ≠ s) : zmodRefl p r * zmodRefl p s ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have h0 := congrArg (fun e : Equiv.Perm (ZMod p) => e 0) h
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.Perm.one_apply] at h0
  have h2 : (2 : ZMod p) * (r - s) = 0 := by
    have hkey : (2 : ZMod p) * (r - s) = 2 * r - (2 * s - 0) := by ring
    rw [hkey]
    exact h0
  exact mul_ne_zero (nine3_B_two_ne_zero hp hp2) (sub_ne_zero.mpr hrs) h2

private lemma nine3_B_conj_mem_fibre {m : ℕ} (h : Nine3OddFrame p m π D) {a c : ZMod p}
    {d e : Γ} (hd : d ∈ nine3FibreSet π D a) (he : e ∈ nine3FibreSet π D c) :
    e * d * e⁻¹ ∈ nine3FibreSet π D (2 * c - a) := by
  refine ⟨h.conj d hd.1 e, ?_⟩
  rw [map_mul, map_mul, map_inv, hd.2, he.2, nine3_B_zmodRefl_inv]
  exact nine3_B_zmodRefl_conj c a

private lemma nine3_B_image_conj_fibre {m : ℕ} (h : Nine3OddFrame p m π D) {a c : ZMod p}
    {e : Γ} (he : e ∈ nine3FibreSet π D c) :
    (MulAut.conj e).toMonoidHom '' (nine3FibreSet π D a) =
      nine3FibreSet π D (2 * c - a) := by
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact nine3_B_conj_mem_fibre h hd he
  · intro hx
    have he' : e⁻¹ ∈ nine3FibreSet π D c := by
      have heq : e⁻¹ = e := inv_eq_of_mul_eq_one_right (h.sq e he.1)
      exact ⟨by simpa [heq] using he.1, by rw [map_inv, he.2, nine3_B_zmodRefl_inv]⟩
    have h2 : e⁻¹ * x * (e⁻¹)⁻¹ ∈ nine3FibreSet π D a := by
      have h2' := nine3_B_conj_mem_fibre h hx he'
      rwa [show 2 * c - (2 * c - a) = a by ring] at h2'
    refine ⟨e⁻¹ * x * (e⁻¹)⁻¹, h2, ?_⟩
    show e * (e⁻¹ * x * (e⁻¹)⁻¹) * e⁻¹ = x
    group

private lemma nine3_B_map_conj_closure {m : ℕ} (h : Nine3OddFrame p m π D) {a c : ZMod p}
    {e : Γ} (he : e ∈ nine3FibreSet π D c) :
    Subgroup.map (MulAut.conj e).toMonoidHom (Subgroup.closure (nine3FibreSet π D a)) =
      Subgroup.closure (nine3FibreSet π D (2 * c - a)) := by
  rw [MonoidHom.map_closure, nine3_B_image_conj_fibre h he]

private lemma nine3_B_card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  let G' : Subgroup G := A ⊔ B
  have hAG' : A ≤ G' := le_sup_left
  have hBG' : B ≤ G' := le_sup_right
  have hG'N : G' ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hB
  haveI : (A.subgroupOf G').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAG').mpr hG'N
  have hsup : A.subgroupOf G' ⊔ B.subgroupOf G' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAG' hBG']
    exact Subgroup.subgroupOf_self (H := A ⊔ B)
  have hidx : (A.subgroupOf G').index = (A.subgroupOf G').relIndex (B.subgroupOf G') := by
    rw [← Subgroup.relIndex_top_right (H := A.subgroupOf G'), ← hsup]
    exact Subgroup.relIndex_sup_left (H := B.subgroupOf G') (K := A.subgroupOf G')
  have hcardA : Nat.card ↥(A.subgroupOf G') = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG').toEquiv
  have hcardB : Nat.card ↥(B.subgroupOf G') = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG').toEquiv
  have hcardI : Nat.card ↥(A.subgroupOf G' ⊓ B.subgroupOf G') = Nat.card ↥(A ⊓ B) := by
    have heq : A.subgroupOf G' ⊓ B.subgroupOf G' = (A ⊓ B).subgroupOf G' := by
      ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [heq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_left)).toEquiv
  have h1 : Nat.card ↥(A.subgroupOf G') * (A.subgroupOf G').index = Nat.card ↥G' :=
    Subgroup.card_mul_index (H := A.subgroupOf G')
  have h2 : (A.subgroupOf G').relIndex (B.subgroupOf G') *
      Nat.card ↥(A.subgroupOf G' ⊓ B.subgroupOf G') = Nat.card ↥(B.subgroupOf G') :=
    Subgroup.relIndex_mul_card (H := A.subgroupOf G') (K := B.subgroupOf G')
  rw [hidx, hcardA] at h1
  rw [hcardI, hcardB] at h2
  have h1' : Nat.card (A ⊔ B : Subgroup G) =
      Nat.card A * (A.subgroupOf G').relIndex (B.subgroupOf G') := h1.symm
  rw [h1', ← h2]
  ring

private def nine3_B_gen (π : Γ →* Equiv.Perm (ZMod p)) (D : Set Γ) : Set Γ :=
  {x | ∃ d ∈ D, ∃ e ∈ D, π d = π e ∧ x = d * e}

private def nine3_B_Q0 (π : Γ →* Equiv.Perm (ZMod p)) (D : Set Γ) : Subgroup Γ :=
  Subgroup.closure (nine3_B_gen π D)

private lemma nine3_B_gen_conj {m : ℕ} (h : Nine3OddFrame p m π D) {a : Γ}
    (ha : a ∈ nine3_B_gen π D) (γ : Γ) : γ * a * γ⁻¹ ∈ nine3_B_gen π D := by
  obtain ⟨d, hd, e, he, hde, rfl⟩ := ha
  exact ⟨γ * d * γ⁻¹, h.conj d hd γ, γ * e * γ⁻¹, h.conj e he γ, by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hde], by group⟩

private lemma nine3_B_Q0_normal {m : ℕ} (h : Nine3OddFrame p m π D) :
    (nine3_B_Q0 π D).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro γ
  change (Subgroup.closure (nine3_B_gen π D)).map (MulAut.conj γ).toMonoidHom =
    Subgroup.closure (nine3_B_gen π D)
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact nine3_B_gen_conj h ha γ
  · intro hx
    refine ⟨γ⁻¹ * x * (γ⁻¹)⁻¹, by
      simpa only [inv_inv] using nine3_B_gen_conj h hx γ⁻¹, ?_⟩
    show γ * (γ⁻¹ * x * (γ⁻¹)⁻¹) * γ⁻¹ = x
    group

private lemma nine3_B_Q0_le_ker (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (h : Nine3OddFrame p m π D) : nine3_B_Q0 π D ≤ π.ker := by
  rw [nine3_B_Q0, Subgroup.closure_le]
  rintro x ⟨d, hd, e, he, hde, rfl⟩
  change π (d * e) = 1
  rw [map_mul]
  obtain ⟨c, hc⟩ := h.refl d hd
  have hec : π e = zmodRefl p c := by rw [← hde]; exact hc
  rw [hc, hec, nine3_B_zmodRefl_sq]

private noncomputable def nine3_B_repSub {m : ℕ} (h : Nine3OddFrame p m π D) (hm : 0 < m)
    (c : ZMod p) : ↥(nine3FibreSet π D c) :=
  Classical.choice ((Nat.card_pos_iff.mp (by
    change 0 < Nat.card {d : Γ // d ∈ D ∧ π d = zmodRefl p c}
    rw [h.card c]
    exact hm)).1)

private lemma nine3_B_mk_eq_of_mem_fibre {m : ℕ} (h : Nine3OddFrame p m π D) {hm : 0 < m}
    {N : Subgroup Γ} [N.Normal] (hN : nine3_B_Q0 π D ≤ N) {c : ZMod p} {d : Γ}
    (hd : d ∈ nine3FibreSet π D c) :
    (QuotientGroup.mk' N) d = (QuotientGroup.mk' N) (nine3_B_repSub h hm c : Γ) := by
  have hmem : d * (nine3_B_repSub h hm c : Γ) ∈ nine3_B_gen π D :=
    ⟨d, hd.1, _, (nine3_B_repSub h hm c).2.1,
      by rw [hd.2, (nine3_B_repSub h hm c).2.2], rfl⟩
  have h1 : (QuotientGroup.mk' N) d * (QuotientGroup.mk' N) (nine3_B_repSub h hm c : Γ) = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hN (Subgroup.subset_closure hmem)
  have h2 : (QuotientGroup.mk' N) (nine3_B_repSub h hm c : Γ) *
      (QuotientGroup.mk' N) (nine3_B_repSub h hm c : Γ) = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hN (Subgroup.subset_closure ⟨_, (nine3_B_repSub h hm c).2.1, _,
      (nine3_B_repSub h hm c).2.1, rfl, rfl⟩)
  rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right h2]

private lemma nine3_B_image_fibre {m : ℕ} (h : Nine3OddFrame p m π D) {hm : 0 < m}
    {N : Subgroup Γ} [N.Normal] (hN : nine3_B_Q0 π D ≤ N) {c : ZMod p} :
    (QuotientGroup.mk' N) '' (nine3FibreSet π D c) =
      {(QuotientGroup.mk' N) (nine3_B_repSub h hm c : Γ)} := by
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact Set.mem_singleton_iff.mpr (nine3_B_mk_eq_of_mem_fibre h hN hd)
  · intro hx
    exact ⟨(nine3_B_repSub h hm c : Γ), (nine3_B_repSub h hm c).2,
      (Set.mem_singleton_iff.mp hx).symm⟩

private lemma nine3_B_quotient_card (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (h : Nine3OddFrame p m π D) (hm : 0 < m) (N : Subgroup Γ) [N.Normal]
    (hN : nine3_B_Q0 π D ≤ N) (hNker : N ≤ π.ker) : Nat.card (Γ ⧸ N) = 2 * p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let r : ZMod p := 0
  let s : ZMod p := 1
  have hrs : r ≠ s := by
    intro hh
    have h10 : (1 : ZMod p) = 0 := by simpa [r, s] using hh.symm
    exact one_ne_zero h10
  have hmap : Subgroup.map (QuotientGroup.mk' N)
      (Subgroup.closure (nine3FibreSet π D r ∪ nine3FibreSet π D s)) =
      Subgroup.closure
        ((QuotientGroup.mk' N) '' (nine3FibreSet π D r ∪ nine3FibreSet π D s)) :=
    MonoidHom.map_closure _ _
  rw [nine3OddFrame_closure_two hp hp2 h hrs] at hmap
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
  have himg : (QuotientGroup.mk' N) '' (nine3FibreSet π D r ∪ nine3FibreSet π D s) =
      {(QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ),
        (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ)} := by
    rw [Set.image_union, nine3_B_image_fibre h hN (hm := hm),
      nine3_B_image_fibre h hN (hm := hm)]
    rfl
  have hgen : Subgroup.closure ({(QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ),
      (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ)} : Set (Γ ⧸ N)) = ⊤ := by
    rw [hmap, himg]
  have hpowΓ : ((nine3_B_repSub h hm r : Γ) * (nine3_B_repSub h hm s : Γ)) ^ p = 1 := by
    apply h.pow _ (nine3_B_repSub h hm r).2.1 _ (nine3_B_repSub h hm s).2.1
    rw [(nine3_B_repSub h hm r).2.2, (nine3_B_repSub h hm s).2.2]
    intro heq
    exact hrs (zmodRefl_inj hp hp2 heq)
  have hAB : ((QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ) *
      (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ)) ^ p = 1 := by
    rw [← map_mul, ← map_pow, hpowΓ, map_one]
  have hA : (QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ) *
      (QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ) = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hN (Subgroup.subset_closure ⟨_, (nine3_B_repSub h hm r).2.1, _,
      (nine3_B_repSub h hm r).2.1, rfl, rfl⟩)
  have hB : (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ) *
      (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ) = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hN (Subgroup.subset_closure ⟨_, (nine3_B_repSub h hm s).2.1, _,
      (nine3_B_repSub h hm s).2.1, rfl, rfl⟩)
  have hA1 : (QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ) ≠ 1 := by
    intro hh
    have hmem : (nine3_B_repSub h hm r : Γ) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact hh
    have hpi : π (nine3_B_repSub h hm r : Γ) = 1 := MonoidHom.mem_ker.mp (hNker hmem)
    rw [(nine3_B_repSub h hm r).2.2] at hpi
    exact nine3_B_zmodRefl_ne_one hp hp2 r hpi
  have hB1 : (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ) ≠ 1 := by
    intro hh
    have hmem : (nine3_B_repSub h hm s : Γ) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact hh
    have hpi : π (nine3_B_repSub h hm s : Γ) = 1 := MonoidHom.mem_ker.mp (hNker hmem)
    rw [(nine3_B_repSub h hm s).2.2] at hpi
    exact nine3_B_zmodRefl_ne_one hp hp2 s hpi
  have hAB1 : (QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ) *
      (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ) ≠ 1 := by
    intro hh
    have hmem : (nine3_B_repSub h hm r : Γ) * (nine3_B_repSub h hm s : Γ) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      show (QuotientGroup.mk' N) ((nine3_B_repSub h hm r : Γ) *
        (nine3_B_repSub h hm s : Γ)) = 1
      rw [map_mul]
      exact hh
    have hpi : π ((nine3_B_repSub h hm r : Γ) * (nine3_B_repSub h hm s : Γ)) = 1 :=
      MonoidHom.mem_ker.mp (hNker hmem)
    rw [map_mul, (nine3_B_repSub h hm r).2.2, (nine3_B_repSub h hm s).2.2] at hpi
    exact nine3_B_zmodRefl_mul_ne_one hp hp2 hrs hpi
  have horder : orderOf ((QuotientGroup.mk' N) (nine3_B_repSub h hm r : Γ) *
      (QuotientGroup.mk' N) (nine3_B_repSub h hm s : Γ)) = p :=
    orderOf_eq_prime hAB hAB1
  obtain ⟨e⟩ := TauCeti.nonempty_dihedralGroup_mulEquiv (G := Γ ⧸ N)
    hA hB hA1 hB1 (n := p) horder hgen
  have hcard : Nat.card (Γ ⧸ N) = Nat.card (DihedralGroup p) :=
    Nat.card_congr e.symm.toEquiv
  rwa [DihedralGroup.nat_card] at hcard

theorem nine3OddFrame_ker_eq (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p m π D) :
    π.ker = Subgroup.closure {x | ∃ d ∈ D, ∃ e ∈ D, π d = π e ∧ x = d * e} := by
  change π.ker = nine3_B_Q0 π D
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · have hDempty : D = ∅ := by
      ext d
      constructor
      · intro hd
        obtain ⟨c, hc⟩ := h.refl d hd
        have hpos : 0 < Nat.card {d : Γ // d ∈ D ∧ π d = zmodRefl p c} :=
          Nat.card_pos_iff.mpr ⟨⟨d, hd, hc⟩, inferInstance⟩
        rw [h.card c, hm0] at hpos
        exact absurd hpos (lt_irrefl 0)
      · intro hd; exact absurd hd (Set.notMem_empty d)
    have hbot : Subgroup.closure D = (⊥ : Subgroup Γ) := by
      rw [hDempty]; exact Subgroup.closure_empty
    have htop : (⊥ : Subgroup Γ) = ⊤ := by rw [← hbot]; exact h.gen
    haveI : Subsingleton Γ :=
      Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp htop)
    have hQ0bot : nine3_B_Q0 π D = ⊥ := by
      simp [nine3_B_Q0, nine3_B_gen, hDempty]
    rw [hQ0bot]
    exact Subsingleton.elim _ _
  · haveI : (nine3_B_Q0 π D).Normal := nine3_B_Q0_normal h
    have hQ0le : nine3_B_Q0 π D ≤ π.ker := nine3_B_Q0_le_ker hp hp2 h
    have hc0 := nine3_B_quotient_card hp hp2 h hm (nine3_B_Q0 π D) le_rfl hQ0le
    have hck := nine3_B_quotient_card hp hp2 h hm π.ker hQ0le le_rfl
    haveI : (π.ker).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
    have hQ0idx : (nine3_B_Q0 π D).index = 2 * p := by
      rw [Subgroup.index_eq_card]; exact hc0
    have hQidx : (π.ker).index = 2 * p := by
      rw [Subgroup.index_eq_card]; exact hck
    have heq : nine3_B_Q0 π D = π.ker :=
      Subgroup.eq_of_index_dvd_index hQ0le (by rw [hQ0idx, hQidx])
    exact heq.symm

private lemma nine3_B_closure_comm {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p}
    {x y : Γ} (hx : x ∈ Subgroup.closure (nine3FibreSet π D c))
    (hy : y ∈ Subgroup.closure (nine3FibreSet π D c)) : x * y = y * x := by
  have hcomm : (nine3FibreSet π D c).Pairwise Commute := fun a ha b hb _ =>
    h.comm a ha.1 b hb.1 (ha.2.trans hb.2.symm)
  letI : CommGroup ↥(Subgroup.closure (nine3FibreSet π D c)) :=
    Subgroup.closureCommGroupOfComm hcomm
  have hxy := mul_comm (⟨x, hx⟩ : ↥(Subgroup.closure (nine3FibreSet π D c))) ⟨y, hy⟩
  simpa using congrArg Subtype.val hxy

private lemma nine3_B_E_sq {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p} {x : Γ}
    (hx : x ∈ Subgroup.closure (nine3FibreSet π D c)) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h.sq y hy.1
  | one => simp
  | mul a b ha hb iha ihb =>
      have hcomm : a * b = b * a := nine3_B_closure_comm h ha hb
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hcomm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
  | inv a _ iha =>
      rw [inv_eq_of_mul_eq_one_right iha]
      exact iha

private lemma nine3_B_prod_four {G : Type*} [CommGroup G] {u v d : G}
    (hu : u * u = 1) (hv : v * v = 1) (hd : d * d = 1) :
    d * (u * d) * (v * d) * (u * v * d) = 1 := by
  have hkey : d * (u * d) * (v * d) * (u * v * d) =
      (u * u) * (v * v) * (d * d) * (d * d) := by
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hkey, hu, hv, hd]
  simp

private lemma nine3_B_map_conj_Z_self {m : ℕ} (h : Nine3OddFrame p m π D) {r : ZMod p}
    {d : Γ} (hd : d ∈ nine3FibreSet π D r) :
    Subgroup.map (MulAut.conj d).toMonoidHom
        (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) =
      Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker := by
  apply le_antisymm
  · rintro w ⟨z, hz, rfl⟩
    have hz_eq : d * z * d⁻¹ = z := by
      rw [(nine3_B_closure_comm h (Subgroup.subset_closure hd) hz.1), mul_assoc,
        mul_inv_cancel, mul_one]
    show d * z * d⁻¹ ∈ Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker
    rw [hz_eq]
    exact hz
  · intro w hw
    refine ⟨w, hw, ?_⟩
    show d * w * d⁻¹ = w
    rw [(nine3_B_closure_comm h (Subgroup.subset_closure hd) hw.1), mul_assoc,
      mul_inv_cancel, mul_one]

private lemma nine3_B_map_conj_Z_le {m : ℕ} (h : Nine3OddFrame p m π D) {r s : ZMod p}
    {d : Γ} (hd : d ∈ nine3FibreSet π D r) :
    Subgroup.map (MulAut.conj d).toMonoidHom
        (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) ≤
      (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
        (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) := by
  rintro w ⟨y, ⟨hyE, hyQ⟩, rfl⟩
  have hyπ : π y = 1 := MonoidHom.mem_ker.mp hyQ
  have hyconj : y * d * y⁻¹ ∈ nine3FibreSet π D r := by
    refine ⟨h.conj d hd.1 y, ?_⟩
    rw [map_mul, map_mul, map_inv, hd.2, hyπ]
    simp
  have h1 : d * (y * d * y⁻¹) ∈ Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.subset_closure hd) (Subgroup.subset_closure hyconj), ?_⟩
    change π (d * (y * d * y⁻¹)) = 1
    rw [map_mul, hd.2, hyconj.2, nine3_B_zmodRefl_sq]
  have hkey : d * y * d⁻¹ = (d * (y * d * y⁻¹)) * y := by
    rw [inv_eq_of_mul_eq_one_right (h.sq d hd.1)]
    group
  show d * y * d⁻¹ ∈ (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
    (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker)
  rw [hkey]
  exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right ⟨hyE, hyQ⟩)

private lemma nine3_B_ker_conj_mem_fibre {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p}
    {z : Γ} (hz : z ∈ π.ker) {d : Γ} (hd : d ∈ nine3FibreSet π D c) :
    z * d * z⁻¹ ∈ nine3FibreSet π D c := by
  refine ⟨h.conj d hd.1 z, ?_⟩
  rw [map_mul, map_mul, map_inv, hd.2, MonoidHom.mem_ker.mp hz]
  simp

private lemma nine3_B_ker_map_conj_E {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p}
    {z : Γ} (hz : z ∈ π.ker) :
    Subgroup.map (MulAut.conj z).toMonoidHom (Subgroup.closure (nine3FibreSet π D c)) =
      Subgroup.closure (nine3FibreSet π D c) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact nine3_B_ker_conj_mem_fibre h hz hd
  · intro hx
    have hz' : z⁻¹ ∈ π.ker := π.ker.inv_mem hz
    refine ⟨z⁻¹ * x * (z⁻¹)⁻¹, nine3_B_ker_conj_mem_fibre h hz' hx, ?_⟩
    show z * (z⁻¹ * x * (z⁻¹)⁻¹) * z⁻¹ = x
    group

private lemma nine3_B_ker_map_conj_Z {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p}
    {z : Γ} (hz : z ∈ π.ker) :
    Subgroup.map (MulAut.conj z).toMonoidHom
        (Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker) =
      Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker := by
  have hle : ∀ {y : Γ}, y ∈ π.ker →
      Subgroup.map (MulAut.conj y).toMonoidHom
          (Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker) ≤
        Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker := by
    intro y hy
    rintro w ⟨u, ⟨huE, huQ⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have hmap := nine3_B_ker_map_conj_E h (c := c) hy
      rw [← hmap]
      exact ⟨u, huE, rfl⟩
    · exact π.normal_ker.conj_mem u huQ y
  apply le_antisymm (hle hz)
  intro w hw
  have hz' : z⁻¹ ∈ π.ker := π.ker.inv_mem hz
  have hw' : (MulAut.conj z⁻¹).toMonoidHom w ∈
      Subgroup.map (MulAut.conj z⁻¹).toMonoidHom
        (Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker) := ⟨w, hw, rfl⟩
  refine ⟨(MulAut.conj z⁻¹).toMonoidHom w, hle hz' hw', ?_⟩
  show z * (z⁻¹ * w * (z⁻¹)⁻¹) * z⁻¹ = w
  group

private lemma nine3_B_Q_le_normalizer_Z {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p} :
    π.ker ≤ Subgroup.normalizer
      ((Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker : Subgroup Γ) : Set Γ) := by
  intro z hz
  rw [Subgroup.mem_set_normalizer_iff]
  intro w
  constructor
  · intro hw
    have hmap := nine3_B_ker_map_conj_Z h (c := c) hz
    have hmem : (MulAut.conj z).toMonoidHom w ∈
        Subgroup.map (MulAut.conj z).toMonoidHom
          (Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker) := ⟨w, hw, rfl⟩
    rw [hmap] at hmem
    simpa using hmem
  · intro hw
    have hz' : z⁻¹ ∈ π.ker := π.ker.inv_mem hz
    have hmap := nine3_B_ker_map_conj_Z h (c := c) hz'
    have hmem : (MulAut.conj z⁻¹).toMonoidHom ((MulAut.conj z).toMonoidHom w) ∈
        Subgroup.map (MulAut.conj z⁻¹).toMonoidHom
          (Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker) :=
      ⟨(MulAut.conj z).toMonoidHom w, by simpa using hw, rfl⟩
    rw [hmap] at hmem
    have hw' : (MulAut.conj z⁻¹).toMonoidHom ((MulAut.conj z).toMonoidHom w) = w := by
      show z⁻¹ * (z * w * z⁻¹) * (z⁻¹)⁻¹ = w
      group
    rwa [hw'] at hmem

private lemma nine3_B_map_conj_Z_inf {m : ℕ} (h : Nine3OddFrame p m π D) {a c : ZMod p}
    {e : Γ} (he : e ∈ nine3FibreSet π D c) :
    Subgroup.map (MulAut.conj e).toMonoidHom
        (Subgroup.closure (nine3FibreSet π D a) ⊓ π.ker) =
      Subgroup.closure (nine3FibreSet π D (2 * c - a)) ⊓ π.ker := by
  rw [← nine3_B_map_conj_closure h (a := a) (c := c) he]
  apply le_antisymm
  · rintro w ⟨u, ⟨huE, huQ⟩, rfl⟩
    refine ⟨⟨u, huE, rfl⟩, ?_⟩
    change π (e * u * e⁻¹) = 1
    rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp huQ]
    simp
  · rintro w ⟨⟨u, huE, rfl⟩, hwQ⟩
    have huQ : u ∈ π.ker := by
      have hmem : e⁻¹ * (e * u * e⁻¹) * (e⁻¹)⁻¹ ∈ π.ker := by
        have hwu : e * u * e⁻¹ ∈ π.ker := hwQ
        exact π.normal_ker.conj_mem (e * u * e⁻¹) hwu e⁻¹
      have heq : e⁻¹ * (e * u * e⁻¹) * (e⁻¹)⁻¹ = u := by group
      rwa [heq] at hmem
    exact ⟨u, ⟨huE, huQ⟩, rfl⟩

private lemma nine3_B_exists_conj_Z {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Nine3OddFrame p m π D) (hm : 0 < m) (c : ZMod p) :
    ∃ e : Γ, Subgroup.map (MulAut.conj e).toMonoidHom
        (Subgroup.closure (nine3FibreSet π D 0) ⊓ π.ker) =
      Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := nine3_B_two_ne_zero hp hp2
  let t : ZMod p := c * (2 : ZMod p)⁻¹
  have ht : 2 * t - 0 = c := by
    have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    calc 2 * t - 0 = 2 * (c * 2⁻¹) := by ring
      _ = (2 * 2⁻¹) * c := by ring
      _ = c := by rw [h22, one_mul]
  exact ⟨(nine3_B_repSub h hm t : Γ), by
    rw [nine3_B_map_conj_Z_inf h (a := 0) (c := t) (nine3_B_repSub h hm t).2, ht]⟩

private lemma nine3_B_mem_normalizer_conj {G : Type*} [Group G] {H : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ H) : g * x * g⁻¹ ∈ H := by
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have : (MulAut.conj g).toMonoidHom x ∈ H := by
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  simpa using this

private lemma nine3_B_map_conj_Y_le {m : ℕ} (h : Nine3OddFrame p m π D) {r s : ZMod p}
    {d : Γ} (hd : d ∈ nine3FibreSet π D r ∪ nine3FibreSet π D s) :
    Subgroup.map (MulAut.conj d).toMonoidHom
        ((Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
          (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker)) ≤
      (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
        (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) := by
  rw [Subgroup.map_sup]
  rcases hd with hdr | hds
  · exact sup_le ((le_of_eq (nine3_B_map_conj_Z_self h hdr)).trans le_sup_left)
      (nine3_B_map_conj_Z_le h hdr)
  · refine sup_le ?_ ((le_of_eq (nine3_B_map_conj_Z_self h hds)).trans le_sup_right)
    exact (nine3_B_map_conj_Z_le (r := s) (s := r) h hds).trans
      (le_of_eq (sup_comm _ _))

private lemma nine3_B_Y_normal {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Nine3OddFrame p m π D) {r s : ZMod p} (hrs : r ≠ s) :
    ((Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
      (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker)).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  rw [← nine3OddFrame_closure_two hp hp2 h hrs]
  apply (Subgroup.closure_le _).mpr
  intro d hd
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm (nine3_B_map_conj_Y_le h hd)
  have hd' : d⁻¹ ∈ nine3FibreSet π D r ∪ nine3FibreSet π D s := by
    rcases hd with hdr | hds
    · exact Or.inl (by rwa [inv_eq_of_mul_eq_one_right (h.sq d hdr.1)])
    · exact Or.inr (by rwa [inv_eq_of_mul_eq_one_right (h.sq d hds.1)])
  have hle' := nine3_B_map_conj_Y_le h hd'
  have hcomp : (MulAut.conj d).toMonoidHom.comp (MulAut.conj d⁻¹).toMonoidHom =
      MonoidHom.id Γ := by
    ext x
    change d * (d⁻¹ * x * (d⁻¹)⁻¹) * d⁻¹ = x
    group
  have hmono := Subgroup.map_mono (f := (MulAut.conj d).toMonoidHom) hle'
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmono
  exact hmono

theorem nine3OddFrame_ker_eq_sup (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    {r s : ZMod p} (hrs : r ≠ s) :
    π.ker = (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
      (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hYnorm : ((Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
      (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker)).Normal :=
    nine3_B_Y_normal hp hp2 h hrs
  apply le_antisymm
  · conv_lhs => rw [nine3OddFrame_ker_eq hp hp2 h]
    rw [Subgroup.closure_le]
    rintro x ⟨d, hd, e, he, hde, rfl⟩
    obtain ⟨c, hc⟩ := h.refl d hd
    have hec : π e = zmodRefl p c := by rw [← hde]; exact hc
    have hde_mem : d * e ∈ Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker :=
      ⟨Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hd, hc⟩)
          (Subgroup.subset_closure ⟨he, hec⟩),
        by change π (d * e) = 1; rw [map_mul, hc, hec, nine3_B_zmodRefl_sq]⟩
    have h2 : (2 : ZMod p) ≠ 0 := nine3_B_two_ne_zero hp hp2
    let t : ZMod p := (r + c) * (2 : ZMod p)⁻¹
    have ht : 2 * t - r = c := by
      have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      calc 2 * t - r = 2 * ((r + c) * 2⁻¹) - r := rfl
        _ = (2 * 2⁻¹) * (r + c) - r := by ring
        _ = (r + c) - r := by rw [h22, one_mul]
        _ = c := by ring
    let f : Γ := (nine3_B_repSub h (by norm_num : 0 < 4) t : Γ)
    have hf : f ∈ nine3FibreSet π D t := (nine3_B_repSub h (by norm_num : 0 < 4) t).2
    have hE : Subgroup.closure (nine3FibreSet π D c) =
        Subgroup.map (MulAut.conj f).toMonoidHom
          (Subgroup.closure (nine3FibreSet π D r)) := by
      have hmc := nine3_B_map_conj_closure h (a := r) (c := t) (e := f) hf
      rw [ht] at hmc
      exact hmc.symm
    have hZle : Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker ≤
        (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
          (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) := by
      intro w hw
      have hwE : w ∈ Subgroup.map (MulAut.conj f).toMonoidHom
          (Subgroup.closure (nine3FibreSet π D r)) := by
        rw [← hE]; exact hw.1
      obtain ⟨u, huE, hueq⟩ := hwE
      have hu_eq : u = f⁻¹ * w * f := by
        rw [← hueq]
        show u = f⁻¹ * (f * u * f⁻¹) * f
        group
      have huQ : u ∈ π.ker := by
        rw [hu_eq]
        simpa only [inv_inv] using π.normal_ker.conj_mem w hw.2 f⁻¹
      have huZ : u ∈ Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker := ⟨huE, huQ⟩
      have hmaple : Subgroup.map (MulAut.conj f).toMonoidHom
            (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ≤
          (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
            (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) := by
        calc Subgroup.map (MulAut.conj f).toMonoidHom
              (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker)
            ≤ Subgroup.map (MulAut.conj f).toMonoidHom
                ((Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
                  (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker)) :=
              Subgroup.map_mono le_sup_left
          _ = (Subgroup.closure (nine3FibreSet π D r) ⊓ π.ker) ⊔
                (Subgroup.closure (nine3FibreSet π D s) ⊓ π.ker) :=
              Subgroup.Normal.map_conj_eq _ f
      exact hmaple ⟨u, huZ, hueq⟩
    exact hZle hde_mem
  · exact sup_le inf_le_right inf_le_right

theorem nine3OddFrame_ker_not_comm (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) : ¬ ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a := by
  classical
  intro hab
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h01 : (0 : ZMod p) ≠ 1 := (one_ne_zero : (1 : ZMod p) ≠ 0).symm
  let F : ZMod p → Set Γ := nine3FibreSet π D
  let d : Γ := (nine3_B_repSub h (by norm_num : 0 < 4) 0 : Γ)
  have hdF : d ∈ F 0 := (nine3_B_repSub h (by norm_num : 0 < 4) 0).2
  let Z1 : Subgroup Γ := Subgroup.closure (F 1) ⊓ π.ker
  let κ : ↥Z1 →* Γ :=
    { toFun := fun z => (z : Γ) * d * (z : Γ)⁻¹ * d⁻¹
      map_one' := by simp
      map_mul' := by
        intro z w
        have hzQ : (z : Γ) ∈ π.ker := z.2.2
        have hwQ : (w : Γ) ∈ π.ker := w.2.2
        have hkwQ : (w : Γ) * d * (w : Γ)⁻¹ * d⁻¹ ∈ π.ker := by
          change π ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹) = 1
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.mp hwQ]
          group
        have hkzQ : (z : Γ) * d * (z : Γ)⁻¹ * d⁻¹ ∈ π.ker := by
          change π ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) = 1
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.mp hzQ]
          group
        show (z : Γ) * (w : Γ) * d * ((z : Γ) * (w : Γ))⁻¹ * d⁻¹ =
          ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) * ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹)
        calc (z : Γ) * (w : Γ) * d * ((z : Γ) * (w : Γ))⁻¹ * d⁻¹
            = (z : Γ) * ((w : Γ) * d * (w : Γ)⁻¹) * (z : Γ)⁻¹ * d⁻¹ := by group
          _ = (z : Γ) * ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹) * (z : Γ)⁻¹ *
                ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) := by group
          _ = ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹) *
                ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) := by
                rw [hab (z : Γ) hzQ ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹) hkwQ]
                group
          _ = ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) *
                ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹) :=
                (hab ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) hkzQ
                  ((w : Γ) * d * (w : Γ)⁻¹ * d⁻¹) hkwQ).symm }
  have hcommF0 : (F 0).Pairwise Commute := fun a ha b hb _ =>
    h.comm a ha.1 b hb.1 (ha.2.trans hb.2.symm)
  let E0 : Subgroup Γ := Subgroup.closure (F 0)
  letI : CommGroup ↥E0 := Subgroup.closureCommGroupOfComm hcommF0
  have hM_le : κ.range ≤ E0 ⊓ π.ker := by
    rintro w ⟨z, rfl⟩
    have hzF : (z : Γ) * d * (z : Γ)⁻¹ ∈ F 0 :=
      nine3_B_ker_conj_mem_fibre h z.2.2 hdF
    refine ⟨?_, ?_⟩
    · show (z : Γ) * d * (z : Γ)⁻¹ * d⁻¹ ∈ E0
      exact Subgroup.mul_mem _ (Subgroup.subset_closure hzF)
        (Subgroup.inv_mem _ (Subgroup.subset_closure hdF))
    · change π ((z : Γ) * d * (z : Γ)⁻¹ * d⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.mp z.2.2]
      group
  have hM_sub : ∀ m ∈ κ.range, (m : Γ) * d ∈ F 0 := by
    rintro m ⟨z, rfl⟩
    have hzF : (z : Γ) * d * (z : Γ)⁻¹ ∈ F 0 :=
      nine3_B_ker_conj_mem_fibre h z.2.2 hdF
    show (z : Γ) * d * (z : Γ)⁻¹ * d⁻¹ * d ∈ F 0
    rwa [show (z : Γ) * d * (z : Γ)⁻¹ * d⁻¹ * d = (z : Γ) * d * (z : Γ)⁻¹ by group]
  have hF_sub : ∀ d' ∈ F 0, d' * d ∈ κ.range := by
    intro d' hd'
    obtain ⟨z, hz, hzd⟩ := h.trans 0 1 h01 d hdF.1 hdF.2 d' hd'.1 hd'.2
    refine ⟨⟨z, hz⟩, ?_⟩
    show (z : Γ) * d * (z : Γ)⁻¹ * d⁻¹ = d' * d
    rw [hzd, inv_eq_of_mul_eq_one_right (h.sq d hdF.1)]
  have hcardF : Nat.card ↥(F 0) = 4 := h.card 0
  have hMcard : Nat.card ↥(κ.range) = 4 := by
    refine (Nat.card_congr ?_).trans hcardF
    refine
      { toFun := fun w => ⟨(w : Γ) * d, hM_sub w w.2⟩
        invFun := fun e => ⟨(e : Γ) * d, hF_sub e e.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro w
      apply Subtype.ext
      show ((w : Γ) * d) * d = (w : Γ)
      rw [mul_assoc, h.sq d hdF.1, mul_one]
    · intro e
      apply Subtype.ext
      show ((e : Γ) * d) * d = (e : Γ)
      rw [mul_assoc, h.sq d hdF.1, mul_one]
  haveI : Fintype ↥(κ.range) := Fintype.ofFinite _
  have hcard4 : Fintype.card ↥(κ.range) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hMcard
  obtain ⟨u, hu_ne⟩ := Fintype.exists_ne_of_one_lt_card (α := ↥(κ.range))
    (by rw [hcard4]; norm_num) (1 : ↥(κ.range))
  have hpair : ({1, u} : Finset ↥(κ.range)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hu_ne.symm), Finset.card_singleton]
  have hlt : ({1, u} : Finset ↥(κ.range)).card < (Finset.univ : Finset ↥(κ.range)).card := by
    rw [hpair, Finset.card_univ, hcard4]; norm_num
  obtain ⟨v, -, hv_notin⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hv_ne1 : v ≠ 1 := by
    intro hv; exact hv_notin (by simp [hv])
  have hvu : v ≠ u := by
    intro hv; exact hv_notin (by simp [hv])
  have hMsq : ∀ m : ↥(κ.range), (m : Γ) * (m : Γ) = 1 :=
    fun m => nine3_B_E_sq h (hM_le m.2).1
  have hdu : d ≠ (u : Γ) * d := by
    intro heq
    have h1 : (1 : Γ) * d = (u : Γ) * d := by simpa using heq
    exact hu_ne (Subtype.ext (mul_right_cancel h1).symm)
  have hdv : d ≠ (v : Γ) * d := by
    intro heq
    have h1 : (1 : Γ) * d = (v : Γ) * d := by simpa using heq
    exact hv_ne1 (Subtype.ext (mul_right_cancel h1).symm)
  have hduv : d ≠ ((u : Γ) * (v : Γ)) * d := by
    intro heq
    have h1 : (1 : Γ) * d = ((u : Γ) * (v : Γ)) * d := by simpa using heq
    have h2 : (1 : Γ) = (u : Γ) * (v : Γ) := mul_right_cancel h1
    have h3 : (u : Γ) = (v : Γ) := by
      calc (u : Γ) = (u : Γ) * 1 := (mul_one _).symm
        _ = (u : Γ) * ((u : Γ) * (v : Γ)) := by rw [← h2]
        _ = ((u : Γ) * (u : Γ)) * (v : Γ) := by group
        _ = (v : Γ) := by rw [hMsq u, one_mul]
    exact hvu (Subtype.ext h3).symm
  have hbdu : (u : Γ) * d ≠ (v : Γ) * d := by
    intro heq
    exact hvu (Subtype.ext (mul_right_cancel heq)).symm
  have hbduv : (u : Γ) * d ≠ ((u : Γ) * (v : Γ)) * d := by
    intro heq
    have h1 : (u : Γ) = (u : Γ) * (v : Γ) := mul_right_cancel heq
    have h2 : (v : Γ) = 1 := by
      calc (v : Γ) = 1 * (v : Γ) := (one_mul _).symm
        _ = ((u : Γ)⁻¹ * (u : Γ)) * (v : Γ) := by rw [inv_mul_cancel]
        _ = (u : Γ)⁻¹ * ((u : Γ) * (v : Γ)) := by group
        _ = (u : Γ)⁻¹ * (u : Γ) := by rw [← h1]
        _ = 1 := inv_mul_cancel _
    exact hv_ne1 (Subtype.ext h2)
  have hcduv : (v : Γ) * d ≠ ((u : Γ) * (v : Γ)) * d := by
    intro heq
    have h1 : (v : Γ) = (u : Γ) * (v : Γ) := mul_right_cancel heq
    have h2 : (u : Γ) = 1 := by
      have h3 : (v : Γ) * (v : Γ)⁻¹ = ((u : Γ) * (v : Γ)) * (v : Γ)⁻¹ := by rw [← h1]
      simpa [mul_assoc] using h3.symm
    exact hu_ne (Subtype.ext h2)
  have hl_nodup : [d, (u : Γ) * d, (v : Γ) * d, ((u : Γ) * (v : Γ)) * d].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true, not_or]
    exact ⟨⟨hdu, hdv, hduv⟩, ⟨hbdu, hbduv⟩, hcduv⟩
  have huE : (u : Γ) ∈ E0 := (hM_le u.2).1
  have hvE : (v : Γ) ∈ E0 := (hM_le v.2).1
  have hdE : d ∈ E0 := Subgroup.subset_closure hdF
  have hU2 : (⟨(u : Γ), huE⟩ : ↥E0) * ⟨(u : Γ), huE⟩ = 1 := Subtype.ext (hMsq u)
  have hV2 : (⟨(v : Γ), hvE⟩ : ↥E0) * ⟨(v : Γ), hvE⟩ = 1 := Subtype.ext (hMsq v)
  have hD2 : (⟨d, hdE⟩ : ↥E0) * ⟨d, hdE⟩ = 1 := Subtype.ext (h.sq d hdF.1)
  have hprodE0 : (⟨d, hdE⟩ : ↥E0) * (⟨(u : Γ), huE⟩ * ⟨d, hdE⟩) *
      (⟨(v : Γ), hvE⟩ * ⟨d, hdE⟩) *
      ((⟨(u : Γ), huE⟩ * ⟨(v : Γ), hvE⟩) * ⟨d, hdE⟩) = 1 :=
    nine3_B_prod_four hU2 hV2 hD2
  have hprodΓ : d * ((u : Γ) * d) * ((v : Γ) * d) * (((u : Γ) * (v : Γ)) * d) = 1 := by
    have hh := congrArg Subtype.val hprodE0
    simpa using hh
  have hl_mem : ∀ x ∈ [d, (u : Γ) * d, (v : Γ) * d, ((u : Γ) * (v : Γ)) * d],
      x ∈ D ∧ π x = zmodRefl p 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hdF
    · exact hM_sub u u.2
    · exact hM_sub v v.2
    · exact hM_sub (u * v) (u * v).2
  have hl_prod : [d, (u : Γ) * d, (v : Γ) * d, ((u : Γ) * (v : Γ)) * d].prod = 1 := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hprodΓ
  exact hi 0 _ hl_nodup (by simp) hl_mem hl_prod

theorem nine3OddFrame_card_ker (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) : Nat.card ↥π.ker = 32 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h01 : (0 : ZMod p) ≠ 1 := (one_ne_zero : (1 : ZMod p) ≠ 0).symm
  let Z : ZMod p → Subgroup Γ := fun c => Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker
  have hZr : Nat.card ↥(Z 0) = 8 := nine3OddFrame_card_inf_ker hp hp2 h hi 0
  have hZs : Nat.card ↥(Z 1) = 8 := nine3OddFrame_card_inf_ker hp hp2 h hi 1
  have hsup : Z 0 ⊔ Z 1 = π.ker := by
    rw [← nine3OddFrame_ker_eq_sup hp hp2 h h01]
  have hCeq : Z 0 ⊓ Z 1 = Subgroup.closure (nine3FibreSet π D 0) ⊓
      Subgroup.closure (nine3FibreSet π D 1) ⊓ π.ker := by
    ext x; simp only [Z, Subgroup.mem_inf]; tauto
  have hCcard_le : Nat.card ↥(Z 0 ⊓ Z 1) ≤ 2 := by
    rw [hCeq]
    exact nine3OddFrame_card_inf_le_two hp hp2 h hi h01
  have hBnorm : Z 1 ≤ Subgroup.normalizer (Z 0 : Set Γ) :=
    (inf_le_right : Z 1 ≤ π.ker).trans (nine3_B_Q_le_normalizer_Z h (c := 0))
  have hCne : Z 0 ⊓ Z 1 ≠ ⊥ := by
    intro hCbot
    apply nine3OddFrame_ker_not_comm hp hp2 h hi
    have hQN0 : π.ker ≤ Subgroup.normalizer (Z 0 : Set Γ) := nine3_B_Q_le_normalizer_Z h (c := 0)
    have hQN1 : π.ker ≤ Subgroup.normalizer (Z 1 : Set Γ) := nine3_B_Q_le_normalizer_Z h (c := 1)
    have hcomm : (Z 0 ∪ Z 1 : Set Γ).Pairwise Commute := by
      intro x hx y hy _
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact nine3_B_closure_comm h hx.1 hy.1
      · rw [← commutatorElement_eq_one_iff_commute]
        have h1 : ⁅x, y⁆ ∈ Z 0 := by
          rw [commutatorElement_def]
          rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
          exact Subgroup.mul_mem _ hx
            (nine3_B_mem_normalizer_conj (hQN0 hy.2) (Subgroup.inv_mem _ hx))
        have h2 : ⁅x, y⁆ ∈ Z 1 := by
          rw [commutatorElement_def]
          rw [show x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ by group]
          exact Subgroup.mul_mem _
            (nine3_B_mem_normalizer_conj (hQN1 hx.2) hy) (Subgroup.inv_mem _ hy)
        have hmem : ⁅x, y⁆ ∈ Z 0 ⊓ Z 1 := ⟨h1, h2⟩
        rw [hCbot, Subgroup.mem_bot] at hmem
        exact hmem
      · rw [← commutatorElement_eq_one_iff_commute]
        have h1 : ⁅x, y⁆ ∈ Z 0 := by
          rw [commutatorElement_def]
          rw [show x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ by group]
          exact Subgroup.mul_mem _
            (nine3_B_mem_normalizer_conj (hQN0 hx.2) hy) (Subgroup.inv_mem _ hy)
        have h2 : ⁅x, y⁆ ∈ Z 1 := by
          rw [commutatorElement_def]
          rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
          exact Subgroup.mul_mem _ hx
            (nine3_B_mem_normalizer_conj (hQN1 hy.2) (Subgroup.inv_mem _ hx))
        have hmem : ⁅x, y⁆ ∈ Z 0 ⊓ Z 1 := ⟨h1, h2⟩
        rw [hCbot, Subgroup.mem_bot] at hmem
        exact hmem
      · exact nine3_B_closure_comm h hx.1 hy.1
    letI : CommGroup ↥(Subgroup.closure ((Z 0 ∪ Z 1 : Set Γ))) :=
      Subgroup.closureCommGroupOfComm hcomm
    have hQeq : Subgroup.closure ((Z 0 ∪ Z 1 : Set Γ)) = π.ker := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hsup]
    intro a ha b hb
    have hh := mul_comm (⟨a, hQeq ▸ ha⟩ : ↥(Subgroup.closure (Z 0 ∪ Z 1 : Set Γ)))
      ⟨b, hQeq ▸ hb⟩
    simpa using congrArg Subtype.val hh
  have hCcard : Nat.card ↥(Z 0 ⊓ Z 1) = 2 := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
    haveI : Nontrivial ↥(Z 0 ⊓ Z 1) := ⟨a, 1, ha1⟩
    haveI : Fintype ↥(Z 0 ⊓ Z 1) := Fintype.ofFinite _
    have h2 : 2 ≤ Nat.card ↥(Z 0 ⊓ Z 1) := by
      rw [Nat.card_eq_fintype_card]
      have := Fintype.one_lt_card (α := ↥(Z 0 ⊓ Z 1))
      omega
    omega
  have hcard := nine3_B_card_sup_mul_card_inf_of_le_normalizer (Z 0) (Z 1) hBnorm
  rw [hsup, hZr, hZs, hCcard] at hcard
  omega

theorem nine3OddFrame_prime_le_five (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) : p ≤ 5 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h01 : (0 : ZMod p) ≠ 1 := (one_ne_zero : (1 : ZMod p) ≠ 0).symm
  let Z : ZMod p → Subgroup Γ := fun c => Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker
  have hZcard : ∀ c, Nat.card ↥(Z c) = 8 := fun c => nine3OddFrame_card_inf_ker hp hp2 h hi c
  have hsup : Z 0 ⊔ Z 1 = π.ker := by
    rw [← nine3OddFrame_ker_eq_sup hp hp2 h h01]
  have hBnorm : Z 1 ≤ Subgroup.normalizer (Z 0 : Set Γ) :=
    (inf_le_right : Z 1 ≤ π.ker).trans (nine3_B_Q_le_normalizer_Z h (c := 0))
  have hCcard : Nat.card ↥(Z 0 ⊓ Z 1) = 2 := by
    have hcard := nine3_B_card_sup_mul_card_inf_of_le_normalizer (Z 0) (Z 1) hBnorm
    rw [hsup, hZcard 0, hZcard 1, nine3OddFrame_card_ker hp hp2 h hi] at hcard
    omega
  have hCcenter : (Z 0 ⊓ Z 1 : Subgroup Γ) ≤ Subgroup.center Γ := by
    have heq : Z 0 ⊓ Z 1 = Subgroup.closure (nine3FibreSet π D 0) ⊓
        Subgroup.closure (nine3FibreSet π D 1) ⊓ π.ker := by
      ext x; simp only [Z, Subgroup.mem_inf]; tauto
    rw [heq]
    exact nine3OddFrame_inf_le_center hp hp2 h h01
  have hCle : ∀ c, Z 0 ⊓ Z 1 ≤ Z c := by
    intro c
    obtain ⟨e, he⟩ := nine3_B_exists_conj_Z hp hp2 h (by norm_num : 0 < 4) c
    show Z 0 ⊓ Z 1 ≤ Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker
    rw [← he]
    intro x hx
    have hxC0 : x ∈ Z 0 := hx.1
    have hcomm : e * x = x * e := Subgroup.mem_center_iff.mp (hCcenter hx) e
    refine ⟨x, hxC0, ?_⟩
    show e * x * e⁻¹ = x
    rw [hcomm]; group
  have hZinf : ∀ {c c' : ZMod p}, c ≠ c' → Z c ⊓ Z c' = Z 0 ⊓ Z 1 := by
    intro c c' hcc
    have hKcard : Nat.card ↥(Z c ⊓ Z c') ≤ 2 := by
      have heq : Z c ⊓ Z c' = Subgroup.closure (nine3FibreSet π D c) ⊓
          Subgroup.closure (nine3FibreSet π D c') ⊓ π.ker := by
        ext x; simp only [Z, Subgroup.mem_inf]; tauto
      rw [heq]
      exact nine3OddFrame_card_inf_le_two hp hp2 h hi hcc
    exact (Subgroup.eq_of_le_of_card_ge (le_inf (hCle c) (hCle c'))
      (by rw [hCcard]; exact hKcard)).symm
  haveI : Fintype ↥(π.ker) := Fintype.ofFinite _
  haveI : Fintype ↥(Z 0 ⊓ Z 1) := Fintype.ofFinite _
  haveI : ∀ c : ZMod p, Fintype ↥(Z c) := fun c => Fintype.ofFinite _
  let α := Σ c : ZMod p, {y : ↥(Z c) // (y : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)}
  have hαcard : Fintype.card α = p * 6 := by
    change Fintype.card (Σ c : ZMod p,
      {y : ↥(Z c) // (y : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)}) = p * 6
    rw [show Fintype.card (Σ c : ZMod p,
        {y : ↥(Z c) // (y : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)}) =
        ∑ c, Fintype.card {y : ↥(Z c) // (y : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)}
      from Fintype.card_sigma]
    have hterm : ∀ c, Fintype.card {y : ↥(Z c) // (y : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)} = 6 := by
      intro c
      rw [Fintype.card_subtype_compl (fun y : ↥(Z c) => (y : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ))]
      have h1 : Fintype.card ↥(Z c) = 8 := by rw [← Nat.card_eq_fintype_card]; exact hZcard c
      have h2 : Fintype.card {y : ↥(Z c) // (y : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ)} = 2 := by
        let e : {y : ↥(Z c) // (y : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ)} ≃ ↥(Z 0 ⊓ Z 1) :=
          { toFun := fun y => ⟨(y.1 : Γ), y.2⟩
            invFun := fun x => ⟨⟨(x : Γ), hCle c x.2⟩, x.2⟩
            left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
            right_inv := fun x => rfl }
        rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
        exact hCcard
      rw [h1, h2]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    simp
  have hβcard : Fintype.card {x : ↥(π.ker) // (x : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)} = 30 := by
    rw [Fintype.card_subtype_compl (fun x : ↥(π.ker) => (x : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ))]
    have h1 : Fintype.card ↥(π.ker) = 32 := by
      rw [← Nat.card_eq_fintype_card]; exact nine3OddFrame_card_ker hp hp2 h hi
    have h2 : Fintype.card {x : ↥(π.ker) // (x : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ)} = 2 := by
      let e : {x : ↥(π.ker) // (x : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ)} ≃ ↥(Z 0 ⊓ Z 1) :=
        { toFun := fun x => ⟨(x.1 : Γ), x.2⟩
          invFun := fun x => ⟨⟨(x : Γ), (inf_le_right : Z 1 ≤ π.ker)
            ((inf_le_right : Z 0 ⊓ Z 1 ≤ Z 1) x.2)⟩, x.2⟩
          left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun x => rfl }
      rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
      exact hCcard
    rw [h1, h2]
  let f : α → {x : ↥(π.ker) // (x : Γ) ∉ (Z 0 ⊓ Z 1 : Subgroup Γ)} := fun a =>
    ⟨⟨(a.2.1 : Γ), (inf_le_right : Z a.1 ≤ π.ker) a.2.1.2⟩, a.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, y, hy⟩ ⟨c', y', hy'⟩ heq
    have hyy : ((y : ↥(Z c)) : Γ) = ((y' : ↥(Z c')) : Γ) :=
      Subtype.ext_iff.mp (Subtype.ext_iff.mp heq)
    have hcc : c = c' := by
      by_contra hne
      have hyC : ((y : ↥(Z c)) : Γ) ∈ (Z 0 ⊓ Z 1 : Subgroup Γ) := by
        have h1 : ((y : ↥(Z c)) : Γ) ∈ Z c := y.2
        have h2 : ((y : ↥(Z c)) : Γ) ∈ Z c' := by rw [hyy]; exact y'.2
        have : ((y : ↥(Z c)) : Γ) ∈ Z c ⊓ Z c' := ⟨h1, h2⟩
        rwa [hZinf hne] at this
      exact hy hyC
    subst hcc
    have hyy' : y = y' := Subtype.ext hyy
    subst hyy'
    rfl
  have hle := Fintype.card_le_of_injective f hf
  rw [hαcard, hβcard] at hle
  omega

end CFSG.LocalAnalysis.WeakClosure81
