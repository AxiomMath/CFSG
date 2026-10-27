module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.YGroups.Y443.EvenPresentation
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.OddStandard.Solomon75
open CFSG.LieType.HighestRoot (mem_center_SL23_iff card_SL23)

private def p6Swap : MulAut (SL23 × SL23) := MulEquiv.prodComm

private lemma p6Swap_apply (a b : SL23) : p6Swap (a, b) = (b, a) := rfl

private lemma p6Swap_mul_self : p6Swap * p6Swap = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  simp [p6Swap_apply]

private def p6Act : Multiplicative (ZMod 2) →* MulAut (SL23 × SL23) :=
  CFSG.YGroups.Y443.z2Hom p6Swap p6Swap_mul_self

private lemma p6Act_gen : p6Act (Multiplicative.ofAdd 1) = p6Swap :=
  CFSG.YGroups.Y443.z2Hom_ofAdd_one _ _

private def psiOne {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23) : SL23 →* G :=
  L1.subtype.comp e.symm.toMonoidHom

private def psiTwo {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23) (h : G) :
    SL23 →* G :=
  (MulAut.conj h).toMonoidHom.comp (psiOne e)

private lemma psiOne_apply {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23)
    (a : SL23) : psiOne e a = ((e.symm a : ↥L1) : G) := rfl

private lemma psiTwo_apply {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23) (h : G)
    (a : SL23) : psiTwo e h a = h * psiOne e a * h⁻¹ := rfl

private lemma psiOne_injective {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23) :
    Function.Injective (psiOne e) := by
  intro a b hab
  exact e.symm.injective (Subtype.ext hab)

private lemma psiTwo_injective {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23)
    (h : G) : Function.Injective (psiTwo e h) := by
  intro a b hab
  exact psiOne_injective e ((MulAut.conj h).injective hab)

private lemma psiOne_range {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23) :
    (psiOne e).range = L1 := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact (e.symm a).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp [psiOne]⟩

private lemma psiOne_mem {G : Type*} [Group G] {L1 : Subgroup G} (e : ↥L1 ≃* SL23)
    (a : SL23) : psiOne e a ∈ L1 := by
  have h : psiOne e a ∈ (psiOne e).range := ⟨a, rfl⟩
  rwa [psiOne_range e] at h

private lemma conj_conj_eq_self {G : Type*} [Group G] {h : G} (hh : h * h = 1) (x : G) :
    h * (h * x * h⁻¹) * h⁻¹ = x := by
  calc h * (h * x * h⁻¹) * h⁻¹ = (MulAut.conj h * MulAut.conj h) x := by
        rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
    _ = (MulAut.conj (h * h) : MulAut G) x := by rw [map_mul]
    _ = x := by rw [hh, map_one, MulAut.one_apply]

private lemma psiTwo_range {G : Type*} [Group G] {L1 L2 : Subgroup G} {h : G}
    (e : ↥L1 ≃* SL23) (hs1 : ∀ x ∈ L1, h * x * h⁻¹ ∈ L2)
    (hs2 : ∀ x ∈ L2, h * x * h⁻¹ ∈ L1) (hh : h * h = 1) :
    (psiTwo e h).range = L2 := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [psiTwo_apply]
    exact hs1 _ (psiOne_mem e a)
  · intro hy
    have hx : h * y * h⁻¹ ∈ L1 := hs2 y hy
    refine ⟨e ⟨h * y * h⁻¹, hx⟩, ?_⟩
    rw [psiTwo_apply, psiOne_apply, MulEquiv.symm_apply_apply]
    exact conj_conj_eq_self hh y

private lemma psiTwo_mem {G : Type*} [Group G] {L1 L2 : Subgroup G} {h : G}
    (e : ↥L1 ≃* SL23) (hs1 : ∀ x ∈ L1, h * x * h⁻¹ ∈ L2)
    (hs2 : ∀ x ∈ L2, h * x * h⁻¹ ∈ L1) (hh : h * h = 1) (b : SL23) :
    psiTwo e h b ∈ L2 := by
  rw [← psiTwo_range e hs1 hs2 hh]
  exact ⟨b, rfl⟩

private theorem exists_hom_of_sl23_swap {G : Type*} [Group G] {L1 L2 : Subgroup G} {h : G}
    (hL1 : Nonempty (↥L1 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hs1 : ∀ x ∈ L1, h * x * h⁻¹ ∈ L2)
    (hs2 : ∀ x ∈ L2, h * x * h⁻¹ ∈ L1)
    (hh : h * h = 1) (hn : h ∉ L1 ⊔ L2) :
    ∃ Φ : (SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2) →* G,
      Φ.range = L1 ⊔ L2 ⊔ Subgroup.zpowers h ∧
      Φ.ker = Subgroup.zpowers (SemidirectProduct.inl ((-1 : SL23), (-1 : SL23))) ∧
      Nat.card ↥Φ.range = 576 := by
  classical
  obtain ⟨e⟩ := hL1
  have hinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  have hneg1 : (-1 : SL23) ≠ 1 := by decide
  have hneg_sq : (-1 : SL23) * (-1) = 1 := by decide
  have hneg_center : (-1 : SL23) ∈ Subgroup.center SL23 :=
    (mem_center_SL23_iff _).mpr (Or.inr rfl)
  have hc_center : (e.symm (-1) : ↥L1) ∈ Subgroup.center ↥L1 :=
    Subgroup.map_center_le_center (f := e.symm.toMonoidHom) e.symm.surjective
      (Subgroup.mem_map_of_mem e.symm.toMonoidHom hneg_center)
  have hc_map : psiOne e (-1) ∈ (Subgroup.center L1).map L1.subtype := by
    have h := Subgroup.mem_map_of_mem L1.subtype hc_center
    simpa [psiOne_apply] using h
  have hc_inf : psiOne e (-1) ∈ L1 ⊓ L2 := by
    rw [hinf]
    exact hc_map
  have hc_sq : psiOne e (-1) * psiOne e (-1) = 1 := by
    rw [← map_mul, hneg_sq, map_one]
  have hc_ne : psiOne e (-1) ≠ 1 := by
    intro h1
    have h2 : (e.symm (-1) : ↥L1) = 1 := Subtype.ext h1
    have h3 : (-1 : SL23) = 1 := by
      have h4 := congrArg (fun z : ↥L1 => (e z : SL23)) h2
      simpa using h4
    exact hneg1 h3
  have hc_conj_ne : h * psiOne e (-1) * h⁻¹ ≠ 1 := by
    intro h1
    apply hc_ne
    have h2 := congrArg (fun x : G => h * x * h⁻¹) h1
    rw [conj_conj_eq_self hh] at h2
    simpa using h2
  have hc_eq : h * psiOne e (-1) * h⁻¹ = psiOne e (-1) := by
    have hconj_inf : h * psiOne e (-1) * h⁻¹ ∈ L1 ⊓ L2 :=
      ⟨hs2 _ hc_inf.2, hs1 _ hc_inf.1⟩
    have hconj_map : h * psiOne e (-1) * h⁻¹ ∈ (Subgroup.center L1).map L1.subtype := by
      rw [← hinf]
      exact hconj_inf
    obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hconj_map
    have hz_center : e z ∈ Subgroup.center SL23 :=
      Subgroup.map_center_le_center (f := e.toMonoidHom) e.surjective
        (Subgroup.mem_map_of_mem e.toMonoidHom hz)
    rcases (mem_center_SL23_iff _).mp hz_center with h1 | h1
    · exfalso
      have hz1 : z = 1 := by
        apply e.injective
        rw [h1, map_one]
      exact hc_conj_ne (by rw [← hzv, hz1]; rfl)
    · have hz1 : z = e.symm (-1) := by
        apply e.injective
        rw [h1, MulEquiv.apply_symm_apply]
      calc h * psiOne e (-1) * h⁻¹ = ((z : ↥L1) : G) := hzv.symm
        _ = ((e.symm (-1) : ↥L1) : G) := by rw [hz1]
        _ = psiOne e (-1) := rfl
  have hcommψ : ∀ a b : SL23, Commute (psiOne e a) (psiTwo e h b) :=
    fun a b => hcomm _ (psiOne_mem e a) _ (psiTwo_mem e hs1 hs2 hh b)
  set Ψ : SL23 × SL23 →* G := MonoidHom.noncommCoprod (psiOne e) (psiTwo e h) hcommψ with hΨ
  have hΨ_apply : ∀ (a b : SL23), Ψ (a, b) = psiOne e a * psiTwo e h b := fun a b => rfl
  have hΨ_range : Ψ.range = L1 ⊔ L2 := by
    rw [hΨ, MonoidHom.noncommCoprod_range, psiOne_range e, psiTwo_range e hs1 hs2 hh]
  have hkerΨ : ∀ u : SL23 × SL23, Ψ u = 1 → u = 1 ∨ u = (-1, -1) := by
    rintro ⟨a, b⟩ hu
    rw [hΨ_apply] at hu
    have h1 : psiOne e a = (psiTwo e h b)⁻¹ := eq_inv_of_mul_eq_one_left hu
    have hb_mem : psiOne e a ∈ L2 := by
      rw [h1]
      exact Subgroup.inv_mem _ (psiTwo_mem e hs1 hs2 hh b)
    have ha_map : psiOne e a ∈ (Subgroup.center L1).map L1.subtype := by
      rw [← hinf]
      exact ⟨psiOne_mem e a, hb_mem⟩
    obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp ha_map
    have hz_center : e z ∈ Subgroup.center SL23 :=
      Subgroup.map_center_le_center (f := e.toMonoidHom) e.surjective
        (Subgroup.mem_map_of_mem e.toMonoidHom hz)
    have hz' : z = e.symm a := Subtype.ext hzv
    have hca : a ∈ Subgroup.center SL23 := by
      have h := hz_center
      rw [hz', MulEquiv.apply_symm_apply] at h
      exact h
    rcases (mem_center_SL23_iff a).mp hca with rfl | rfl
    · left
      have hψ₂ : psiTwo e h b = 1 := by
        have h := h1
        rw [map_one] at h
        exact inv_eq_one.mp h.symm
      have hb : b = 1 := psiTwo_injective e h (by rw [hψ₂, map_one])
      exact Prod.ext rfl hb
    · right
      have hb : b = -1 := by
        apply psiTwo_injective e h
        calc psiTwo e h b = (psiOne e (-1))⁻¹ := by rw [h1, inv_inv]
          _ = psiOne e (-1) := inv_eq_of_mul_eq_one_right hc_sq
          _ = psiTwo e h (-1) := by rw [psiTwo_apply, hc_eq]
      exact Prod.ext rfl hb
  set fg : Multiplicative (ZMod 2) →* G := CFSG.YGroups.Y443.z2Hom h hh with hfg
  have hfg_one : fg 1 = 1 := map_one fg
  have hfg_gen : fg (Multiplicative.ofAdd 1) = h := CFSG.YGroups.Y443.z2Hom_ofAdd_one h hh
  have hfg_range : fg.range = Subgroup.zpowers h := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rcases CFSG.YGroups.Y443.z2_cases x with rfl | rfl
      · exact Subgroup.one_mem _
      · rw [hfg_gen]
        exact Subgroup.mem_zpowers h
    · rw [Subgroup.zpowers_le]
      exact ⟨Multiplicative.ofAdd 1, hfg_gen⟩
  have hcompat : ∀ g : Multiplicative (ZMod 2), Ψ.comp (p6Act g).toMonoidHom =
      (MulAut.conj (fg g)).toMonoidHom.comp Ψ := by
    intro g
    refine MonoidHom.ext fun u => ?_
    obtain ⟨a, b⟩ := u
    change Ψ ((p6Act g) (a, b)) = fg g * Ψ (a, b) * (fg g)⁻¹
    rcases CFSG.YGroups.Y443.z2_cases g with rfl | rfl
    · rw [hfg_one]
      simp [hΨ_apply]
    · have hgen : (p6Act (Multiplicative.ofAdd (1 : ZMod 2))) (a, b) = (b, a) := by
        rw [p6Act_gen]
        exact p6Swap_apply a b
      rw [hgen, hΨ_apply, hΨ_apply, hfg_gen]
      have key : h * (psiOne e a * psiTwo e h b) * h⁻¹ = psiTwo e h a * psiOne e b := by
        calc h * (psiOne e a * psiTwo e h b) * h⁻¹
            = (h * psiOne e a * h⁻¹) * (h * psiTwo e h b * h⁻¹) := by group
          _ = (h * psiOne e a * h⁻¹) * psiOne e b := by
                rw [psiTwo_apply, conj_conj_eq_self hh]
      rw [key]
      exact hcomm _ (psiOne_mem e b) _ (psiTwo_mem e hs1 hs2 hh a)
  set Φ : (SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2) →* G :=
    SemidirectProduct.lift Ψ fg hcompat with hΦ
  have hΦ_apply : ∀ x : (SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2),
      Φ x = Ψ x.1 * fg x.2 := by
    intro x
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [hΦ, map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  have hrange : Φ.range = L1 ⊔ L2 ⊔ Subgroup.zpowers h := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hΦ_apply]
      have h1 : Ψ x.1 ∈ L1 ⊔ L2 := by
        rw [← hΨ_range]
        exact ⟨x.1, rfl⟩
      have h2 : fg x.2 ∈ Subgroup.zpowers h := by
        rw [← hfg_range]
        exact ⟨x.2, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    · refine sup_le ?_ ?_
      · rw [← hΨ_range]
        rintro _ ⟨n, rfl⟩
        exact ⟨SemidirectProduct.inl n, by rw [hΦ_apply]; simp⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), by rw [hΦ_apply]; simp [hfg_gen]⟩
  have hker : Φ.ker = Subgroup.zpowers (SemidirectProduct.inl ((-1 : SL23), (-1 : SL23))) := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : Ψ x.1 * fg x.2 = 1 := by
        rw [← hΦ_apply]
        exact hx
      rcases CFSG.YGroups.Y443.z2_cases x.2 with h2 | h2
      · have hΨ1 : Ψ x.1 = 1 := by simpa [h2] using hx'
        rcases hkerΨ x.1 hΨ1 with h1 | h1
        · have hx1 : x = 1 := by
            rw [← SemidirectProduct.inl_left_mul_inr_right x, h1, h2]
            simp only [map_one, mul_one]
          rw [hx1]
          exact Subgroup.one_mem _
        · have hx1 : x = SemidirectProduct.inl ((-1 : SL23), (-1 : SL23)) := by
            rw [← SemidirectProduct.inl_left_mul_inr_right x, h1, h2]
            simp only [map_one, mul_one]
          rw [hx1]
          exact Subgroup.mem_zpowers _
      · have hΨ1 : Ψ x.1 = h := by
          have h := eq_inv_of_mul_eq_one_left (by simpa [h2, hfg_gen] using hx')
          rwa [hinv] at h
        exact absurd (by rw [← hΨ_range]; exact ⟨x.1, hΨ1⟩ : h ∈ L1 ⊔ L2) hn
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, hΦ_apply]
      have h1 : Ψ ((-1 : SL23), (-1 : SL23)) = 1 := by
        rw [hΨ_apply, psiTwo_apply, hc_eq]
        exact hc_sq
      simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, hfg_one, mul_one]
      exact h1
  have hN₀_sq : (SemidirectProduct.inl ((-1 : SL23), (-1 : SL23)) :
      (SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2)) ^ 2 = 1 := by
    have hx : ((-1 : SL23), (-1 : SL23)) * ((-1 : SL23), (-1 : SL23)) = 1 := by
      simp [hneg_sq]
    rw [pow_two]
    calc SemidirectProduct.inl ((-1 : SL23), (-1 : SL23)) *
          SemidirectProduct.inl ((-1 : SL23), (-1 : SL23))
        = SemidirectProduct.inl (((-1 : SL23), (-1 : SL23)) *
            ((-1 : SL23), (-1 : SL23))) :=
          (map_mul (SemidirectProduct.inl : SL23 × SL23 →*
            ((SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2))) _ _).symm
      _ = SemidirectProduct.inl (1 : SL23 × SL23) := congrArg _ hx
      _ = 1 := map_one _
  have hN₀_ne : (SemidirectProduct.inl ((-1 : SL23), (-1 : SL23)) :
      (SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2)) ≠ 1 := by
    intro h1
    have h2 : ((-1 : SL23), (-1 : SL23)) = 1 := by
      have h3 : (SemidirectProduct.inl ((-1 : SL23), (-1 : SL23)) :
          (SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2)).left = 1 := by
        rw [h1]
        rfl
      rw [SemidirectProduct.left_inl] at h3
      exact h3
    exact hneg1 (by simpa using congrArg Prod.fst h2)
  have hcard_ker : Nat.card ↥Φ.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hN₀_sq hN₀_ne
  have hcardC : Nat.card ((SL23 × SL23) ⋊[p6Act] Multiplicative (ZMod 2)) = 1152 := by
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [SemidirectProduct.card, Nat.card_prod, card_SL23, h2]
  have hcard_range : Nat.card ↥Φ.range = 576 := by
    have h := Subgroup.card_ker_mul_card_range Φ
    rw [hcard_ker, hcardC] at h
    omega
  exact ⟨Φ, hrange, hker, hcard_range⟩

theorem card_sup_zpowers_of_sl23_swap {G : Type*} [Group G] {L1 L2 : Subgroup G} {h : G}
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hs1 : ∀ x ∈ L1, h * x * h⁻¹ ∈ L2) (hs2 : ∀ x ∈ L2, h * x * h⁻¹ ∈ L1)
    (hh : h * h = 1) (hn : h ∉ L1 ⊔ L2) :
    Nat.card ↥(L1 ⊔ L2 ⊔ Subgroup.zpowers h) = 576 := by
  obtain ⟨Φ, hrange, -, hcard⟩ := exists_hom_of_sl23_swap hL1 hcomm hinf hs1 hs2 hh hn
  rw [← hrange]
  exact hcard

theorem nonempty_mulEquiv_of_sl23_swap {G G' : Type*} [Group G] [Group G']
    {L1 L2 : Subgroup G} {h : G} {L1' L2' : Subgroup G'} {h' : G'}
    (hL1 : Nonempty (↥L1 ≃* SL23)) (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hs1 : ∀ x ∈ L1, h * x * h⁻¹ ∈ L2) (hs2 : ∀ x ∈ L2, h * x * h⁻¹ ∈ L1)
    (hh : h * h = 1) (hn : h ∉ L1 ⊔ L2)
    (hL1' : Nonempty (↥L1' ≃* SL23)) (hcomm' : ∀ x ∈ L1', ∀ y ∈ L2', x * y = y * x)
    (hinf' : L1' ⊓ L2' = (Subgroup.center L1').map L1'.subtype)
    (hs1' : ∀ x ∈ L1', h' * x * h'⁻¹ ∈ L2') (hs2' : ∀ x ∈ L2', h' * x * h'⁻¹ ∈ L1')
    (hh' : h' * h' = 1) (hn' : h' ∉ L1' ⊔ L2') :
    Nonempty (↥(L1 ⊔ L2 ⊔ Subgroup.zpowers h) ≃* ↥(L1' ⊔ L2' ⊔ Subgroup.zpowers h')) := by
  obtain ⟨Φ, hrange, hker, -⟩ := exists_hom_of_sl23_swap hL1 hcomm hinf hs1 hs2 hh hn
  obtain ⟨Φ', hrange', hker', -⟩ := exists_hom_of_sl23_swap hL1' hcomm' hinf' hs1' hs2' hh' hn'
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange Φ).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq (hker.trans hker'.symm)).trans
      ((QuotientGroup.quotientKerEquivRange Φ').trans (MulEquiv.subgroupCongr hrange')))⟩

end CFSG.RankThree.GF2n.Parrott
