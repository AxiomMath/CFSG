module

public import CFSG.RankThree.GF2n.Stroth78.Basic
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAIndex

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.CGT.T75H CFSG.RankThree.GF2n.Tim79a
  CFSG.LargeExtraspecial.Timmesfeld CFSG.GroupTheory.SmallFixedTwoGroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_e_f (S : Setting z E F) {x : G} (hx : x ∈ Q z) :
    ∃ e ∈ E, ∃ f ∈ F, x = e * f := by
  rw [Q_eq_sup S] at hx
  exact exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hx

theorem decomp_involution (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (haZ : a ∉ ZQ z)
    (ha2 : a ^ 2 = 1) :
    ∃ e ∈ E, ∃ f ∈ F, a = e * f ∧ f ^ 2 = 1 ∧ f ∉ centerIn F := by
  obtain ⟨e, he, f, hf, rfl⟩ := exists_e_f S haQ
  have he2 : e * e = 1 := by simpa [pow_two] using S.hyp.elemAbelian.2 e he
  have hf2 : f ^ 2 = 1 := by
    have hsq : (e * f) ^ 2 = f ^ 2 := by
      rw [pow_two, pow_two]
      calc
        (e * f) * (e * f) = e * (f * e) * f := by group
        _ = e * (e * f) * f := by rw [(S.hyp.commute e he f hf).eq]
        _ = (e * e) * (f * f) := by group
        _ = f * f := by rw [he2, one_mul]
    rw [← hsq, ha2]
  refine ⟨e, he, f, hf, rfl, hf2, ?_⟩
  intro hfZ
  apply haZ
  rw [ZQ_eq S]
  have hfz : f ∈ Subgroup.zpowers z := by
    rw [← F_centerIn_eq S]
    exact hfZ
  exact Subgroup.mul_mem_sup he hfz

theorem centralizer_Q_eq (S : Setting z E F) {a f : G} (haQ : a ∈ Q z)
    (hef : ∃ e ∈ E, a = e * f) :
    Subgroup.centralizer ({a} : Set G) ⊓ Q z =
      E ⊔ (Subgroup.centralizer ({f} : Set G) ⊓ F) := by
  obtain ⟨e, he, rfl⟩ := hef
  have hfQ : f ∈ Q z := by
    have h : (e : G)⁻¹ * (e * f) ∈ Q z :=
      Subgroup.mul_mem (Q z) (Subgroup.inv_mem (Q z) (E_le_Q S he)) haQ
    simpa using h
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (S.hyp.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEZ : E ≤ Subgroup.centralizer (Q z : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp (E_le_ZQ S hx)).2
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxcent, hxQ⟩
    rw [Q_eq_sup S] at hxQ
    obtain ⟨e', he', f', hf', rfl⟩ := exists_mul_of_mem_sup_of_comm
      (fun u hu v hv => (S.hyp.commute u hu v hv).eq) hxQ
    have hzero1 : ⁅e', e * f⁆ = 1 := by
      have h1 : Commute e' e := hEab e' he' e he
      have h2 : Commute e' f := (Subgroup.mem_centralizer_iff.mp (hEZ he') f hfQ).symm
      exact (h1.mul_right h2).commutator_eq
    have hzero2 : ⁅f', e⁆ = 1 := (S.hyp.commute e he f' hf').symm.commutator_eq
    have he_deriv : Commute e ⁅f', f⁆ := by
      have hmemQ : ⁅f', f⁆ ∈ Q z := by
        have h1 : ⁅f', f⁆ ∈ ⁅Q z, Q z⁆ :=
          Subgroup.commutator_mem_commutator (F_le_Q S hf') hfQ
        rw [Q_deriv_eq S] at h1
        exact Subgroup.zpowers_le.mpr (z_mem_Q S) h1
      exact (Subgroup.mem_centralizer_iff.mp (hEZ he) ⁅f', f⁆ hmemQ).symm
    have hstep2 : ⁅f', e * f⁆ = ⁅f', f⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hzero2, one_mul, he_deriv.eq, mul_assoc,
        mul_inv_cancel, mul_one]
    have he'_deriv : Commute e' ⁅f', f⁆ := by
      have hmemQ : ⁅f', f⁆ ∈ Q z := by
        have h1 : ⁅f', f⁆ ∈ ⁅Q z, Q z⁆ :=
          Subgroup.commutator_mem_commutator (F_le_Q S hf') hfQ
        rw [Q_deriv_eq S] at h1
        exact Subgroup.zpowers_le.mpr (z_mem_Q S) h1
      exact (Subgroup.mem_centralizer_iff.mp (hEZ he') ⁅f', f⁆ hmemQ).symm
    have hstep1 : ⁅e' * f', e * f⁆ = ⁅f', f⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hzero1, mul_one, hstep2, he'_deriv.eq,
        mul_assoc, mul_inv_cancel, mul_one]
    have hx1 : ⁅e' * f', e * f⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hxcent) (e * f)
        (Set.mem_singleton (e * f))
    have hff' : f' * f = f * f' :=
      commutatorElement_eq_one_iff_mul_comm.mp (by rw [← hstep1]; exact hx1)
    exact Subgroup.mul_mem_sup he' (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hff'.symm), hf'⟩)
  · rintro x hx
    obtain ⟨y, hyE, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_comm
      (fun u hu v hv => (S.hyp.commute u hu v (Subgroup.mem_inf.mp hv).2).eq) hx
    obtain ⟨hwC, hwF⟩ := Subgroup.mem_inf.mp hw
    have hye : Commute y e := hEab y hyE e he
    have hyf : Commute y f := (Subgroup.mem_centralizer_iff.mp (hEZ hyE) f hfQ).symm
    have hwe : Commute w e := (S.hyp.commute e he w hwF).symm
    have hwf : Commute w f :=
      (Subgroup.mem_centralizer_iff.mp hwC f (Set.mem_singleton f)).symm
    have hcommute : Commute (y * w) (e * f) := (hye.mul_right hyf).mul_left (hwe.mul_right hwf)
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mul_mem (Q z) (E_le_Q S hyE) (F_le_Q S hwF)⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcommute.eq.symm

theorem card_centralizer_F (S : Setting z E F) {f : G} (hf : f ∈ F) (hfZ : f ∉ centerIn F) :
    Nat.card ↥(Subgroup.centralizer ({f} : Set G) ⊓ F) = Nat.card F / 2 := by
  have hzF : z ∈ F := Subgroup.commutator_le_self F S.hyp.mem_derived
  let s : ↥F := ⟨f, hf⟩
  let zF : ↥F := ⟨z, hzF⟩
  have hz2 : z ^ 2 = 1 := by simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  have hconj : ∀ g : ↥F, g * s * g⁻¹ = s ∨ g * s * g⁻¹ = zF * s := by
    intro g
    have hmem : ⁅(g : G), f⁆ ∈ Subgroup.zpowers z := by
      rw [← F_deriv_eq_zpowers S]
      exact Subgroup.commutator_mem_commutator g.2 hf
    have hc : ⁅(g : G), f⁆ = 1 ∨ ⁅(g : G), f⁆ = z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · left
        rw [← hk, zpow_mul]
        simp [hz2]
      · right
        rw [← hk, zpow_add, zpow_mul]
        simp [hz2]
    let c : ↥F := ⟨⁅(g : G), f⁆,
      Subgroup.commutator_le_self F (Subgroup.commutator_mem_commutator g.2 hf)⟩
    have hkey : g * s * g⁻¹ = c * s := by
      apply Subtype.ext
      show (g : G) * f * (g : G)⁻¹ = ⁅(g : G), f⁆ * f
      rw [commutatorElement_def]
      group
    rcases hc with h1 | hz
    · left
      rw [hkey, show c = 1 from Subtype.ext h1, one_mul]
    · right
      rw [hkey, show c = zF from Subtype.ext hz]
  have hidx_le : (Subgroup.centralizer ({s} : Set ↥F)).index ≤ 2 :=
    index_centralizer_le_two hconj
  have hidx_ne : (Subgroup.centralizer ({s} : Set ↥F)).index ≠ 1 := by
    intro h1
    have hcard : Nat.card (Subgroup.centralizer ({s} : Set ↥F)) = Nat.card ↥F := by
      have h := Subgroup.card_mul_index (Subgroup.centralizer ({s} : Set ↥F))
      rw [h1, mul_one] at h
      exact h
    have htop : Subgroup.centralizer ({s} : Set ↥F) = ⊤ :=
      Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top, ← hcard])
    apply hfZ
    rw [centerIn_eq_map_center]
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ Subgroup.centralizer ({s} : Set ↥F) := htop ▸ Subgroup.mem_top y
    exact (Subgroup.mem_centralizer_iff.mp hy s (Set.mem_singleton s)).symm
  have hidx : (Subgroup.centralizer ({s} : Set ↥F)).index = 2 := by
    have hpos : (Subgroup.centralizer ({s} : Set ↥F)).index ≠ 0 := by
      intro h0
      have hcard := Subgroup.card_mul_index (Subgroup.centralizer ({s} : Set ↥F))
      rw [h0, mul_zero] at hcard
      exact Nat.card_pos.ne' hcard.symm
    omega
  have hcardT : Nat.card ↥(Subgroup.centralizer ({s} : Set ↥F)) * 2 = Nat.card F := by
    rw [← hidx]
    exact Subgroup.card_mul_index (Subgroup.centralizer ({s} : Set ↥F))
  have hmap : (Subgroup.centralizer ({s} : Set ↥F)).map F.subtype =
      Subgroup.centralizer ({f} : Set G) ⊓ F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
      rw [Set.mem_singleton_iff] at hh
      subst hh
      show (s : G) * (y : G) = (y : G) * (s : G)
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy s (Set.mem_singleton s))
    · rintro ⟨hx1, hx2⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hx2⟩, ?_, rfl⟩
      have hx' : f * x = x * f := Subgroup.mem_centralizer_iff.mp hx1 f (Set.mem_singleton f)
      refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subtype.ext hx'
  calc
    Nat.card ↥(Subgroup.centralizer ({f} : Set G) ⊓ F)
        = Nat.card ↥((Subgroup.centralizer ({s} : Set ↥F)).map F.subtype) := by rw [hmap]
    _ = Nat.card ↥(Subgroup.centralizer ({s} : Set ↥F)) :=
      Subgroup.card_map_of_injective F.subtype_injective
    _ = Nat.card F / 2 := by
      rw [← hcardT]
      exact (Nat.mul_div_cancel _ (by norm_num : 0 < 2)).symm

theorem card_centralizer_Q (S : Setting z E F) {a f : G} (haQ : a ∈ Q z) (haZ : a ∉ ZQ z)
    (ha2 : a ^ 2 = 1) (hef : ∃ e ∈ E, a = e * f) (hf : f ∈ F) (hfZ : f ∉ centerIn F) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Q z) = Nat.card E * (Nat.card F / 2) := by
  rw [centralizer_Q_eq S haQ hef]
  have hinf : E ⊓ (Subgroup.centralizer ({f} : Set G) ⊓ F) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxE, hxCF⟩ := Subgroup.mem_inf.mp hx
    have hxF : x ∈ F := (Subgroup.mem_inf.mp hxCF).2
    have hxEF : x ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨hxE, hxF⟩
    simpa [S.hyp.inf_eq_bot] using hxEF
  rw [card_sup_of_comm (fun x hx y hy => (S.hyp.commute x hx y (Subgroup.mem_inf.mp hy).2).eq)
    hinf, card_centralizer_F S hf hfZ]

@[expose] def CommutatorOrthogonality (S : Setting z E F) : Prop :=
  ∀ W : Subgroup G, ZQ z ≤ W → W ≤ Q z →
    Nat.card ↥(Subgroup.centralizer (W : Set G) ⊓ Q z) * Nat.card W =
      Nat.card (Q z) * Nat.card (ZQ z)

end CFSG.RankThree.GF2n.Stroth78
