module

public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.S15K.SL2Model
public import CFSG.RankThree.PartOne.KLR.A1Swap
public import CFSG.RankThree.PartOne.KF.ClsCenter

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

section Weyl

variable {Q : Type} [Group Q]

theorem torusImage_top_eq_range (E : Subgroup Q) :
    torusImage E ⊤ = E.normalizerMonoidHom.range := by
  unfold torusImage
  rw [Subgroup.top_subgroupOf, MonoidHom.range_eq_map]

theorem coe_normalizerMonoidHom_apply {E : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.normalizer (E : Set Q)) (e : E) :
    ((E.normalizerMonoidHom ⟨g, hg⟩ e : E) : Q) = g * e * g⁻¹ := rfl

theorem perm3_central_eq_one (ρ : Equiv.Perm (Fin 3))
    (h : ∀ σ : Equiv.Perm (Fin 3), ρ * σ = σ * ρ) : ρ = 1 := by
  revert ρ
  decide +kernel

theorem not_nonempty_perm3_of_inv {p : ℕ} {Ē : Subgroup Q} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsElementaryAbelian p Ē) (hne : Nat.card Ē ≠ 1) {g : Q}
    (hg : g ∈ Subgroup.normalizer (Ē : Set Q)) (hinv : ∀ e ∈ Ē, g * e * g⁻¹ = e⁻¹) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨φ⟩
  set w : MulAut Ē := Ē.normalizerMonoidHom ⟨g, hg⟩ with hw
  have hwmem : w ∈ torusImage Ē ⊤ := by
    rw [torusImage_top_eq_range]
    exact ⟨⟨g, hg⟩, rfl⟩
  have hwe : ∀ e : Ē, ((w e : Ē) : Q) = ((e : Ē) : Q)⁻¹ := fun e => by
    rw [hw, coe_normalizerMonoidHom_apply]
    exact hinv e e.2
  have hcomm : ∀ w' : MulAut Ē, w * w' = w' * w := by
    intro w'
    ext e
    change ((w (w' e) : Ē) : Q) = ((w' (w e) : Ē) : Q)
    rw [hwe]
    have h1 : w e = e⁻¹ := Subtype.ext (by rw [hwe]; rfl)
    rw [h1, map_inv]
    rfl
  have hcen : ∀ σ : Equiv.Perm (Fin 3), φ ⟨w, hwmem⟩ * σ = σ * φ ⟨w, hwmem⟩ := by
    intro σ
    obtain ⟨y, rfl⟩ := φ.surjective σ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm y.1)
  have h1 : φ ⟨w, hwmem⟩ = 1 := perm3_central_eq_one _ hcen
  have h2 : (⟨w, hwmem⟩ : torusImage Ē ⊤) = 1 := (map_eq_one_iff φ φ.injective).1 h1
  have hw1 : w = 1 := congrArg Subtype.val h2
  have hbot : ∀ e : Ē, e = 1 := by
    intro e
    have h3 : (e : Q) = (e : Q)⁻¹ := by
      rw [← hwe e, hw1]
      rfl
    have h4 : (e : Q) * (e : Q) = 1 := by
      calc (e : Q) * (e : Q) = (e : Q) * (e : Q)⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel _
    have h5 : (e : Q) ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Ē) _ e.2
    obtain ⟨k, hk⟩ := (hp.eq_two_or_odd'.resolve_left hp2)
    have h6 : (e : Q) = 1 := by
      rw [hk, pow_succ, pow_mul, sq, h4, one_pow, one_mul] at h5
      exact h5
    exact Subtype.ext h6
  apply hne
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => (hbot a).trans (hbot b).symm⟩, ⟨1⟩⟩

end Weyl

section Sylow

variable {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]

theorem exists_inv_of_sylow (P₀ : Sylow p Q) {g₀ : Q}
    (h : ∀ y ∈ (P₀ : Subgroup Q), g₀ * y * g₀⁻¹ = y⁻¹) {E : Subgroup Q} (hE : IsPGroup p E) :
    ∃ g : Q, ∀ e ∈ E, g * e * g⁻¹ = e⁻¹ := by
  obtain ⟨P, hEP⟩ := hE.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq Q P₀ P
  refine ⟨a * g₀ * a⁻¹, fun e he => ?_⟩
  have heP : e ∈ (P : Subgroup Q) := hEP he
  rw [← ha] at heP
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ (P₀ : Subgroup Q), a * y * a⁻¹ = e := by
    rw [Sylow.smul_def] at heP
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 heP
    exact ⟨y, hy, rfl⟩
  have := h y hy
  calc a * g₀ * a⁻¹ * (a * y * a⁻¹) * (a * g₀ * a⁻¹)⁻¹
      = a * (g₀ * y * g₀⁻¹) * a⁻¹ := by group
    _ = (a * y * a⁻¹)⁻¹ := by rw [this]; group

end Sylow

section Conf

variable {p g : ℕ} {Q : Type} [Group Q] [Finite Q] {Ē : Subgroup Q}

theorem Row8Conf.inf_center_eq_bot (h : Row8Conf p g Q Ē) : Ē ⊓ Subgroup.center Q = ⊥ := by
  obtain ⟨c, hcE, hc1, Kb, x, hKbc, hKbN, hmodel, hxK, hxo, hgen⟩ := h.conf
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.elem
  have hKq := S15K.isQuasisimple_of_model hmodel
  have hKz : Subgroup.center Kb = ⊥ := S15K.center_eq_bot_of_model hmodel
  have hxE : x ∈ Ē := by
    rw [hgen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hcx : c * x = x * c := congrArg Subtype.val (h.elem.is_comm.comm ⟨c, hcE⟩ ⟨x, hxE⟩)
  have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Ē) c hcE
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzE, hzZ⟩ := hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  rw [hgen] at hzE
  obtain ⟨s, hs, u, hu, hzsu⟩ := KLR.exists_mul_of_mem_sup_of_commute
    (A := Subgroup.zpowers c) (B := Subgroup.zpowers x) (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute c x from hcx) i j).eq) hzE
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hxj : x ^ j = 1 := by
    have hmem : x ^ j ∈ Kb := Subgroup.zpow_mem _ hxK j
    have hcen : (⟨x ^ j, hmem⟩ : Kb) ∈ Subgroup.center Kb := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hkc : (k : Q) * c = c * (k : Q) := Subgroup.mem_centralizer_singleton_iff.1
        (hKbc k.2)
      have hkci : (k : Q) * c ^ i = c ^ i * (k : Q) :=
        (Commute.zpow_right (show Commute (k : Q) c from hkc) i).eq
      have hkz : (k : Q) * z = z * (k : Q) := Subgroup.mem_center_iff.1 hzZ (k : Q)
      have hz' : x ^ j = (c ^ i)⁻¹ * z := by
        rw [hzsu]
        group
      change (k : Q) * x ^ j = x ^ j * (k : Q)
      rw [hz']
      calc (k : Q) * ((c ^ i)⁻¹ * z) = ((k : Q) * (c ^ i)⁻¹) * z := by group
        _ = ((c ^ i)⁻¹ * (k : Q)) * z := by
            rw [show (k : Q) * (c ^ i)⁻¹ = (c ^ i)⁻¹ * (k : Q) from
              (Commute.inv_right (show Commute (k : Q) (c ^ i) from hkci)).eq]
        _ = (c ^ i)⁻¹ * ((k : Q) * z) := by group
        _ = (c ^ i)⁻¹ * (z * (k : Q)) := by rw [hkz]
        _ = ((c ^ i)⁻¹ * z) * (k : Q) := by group
    rw [hKz, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hzc : z = c ^ i := by rw [hzsu, hxj, mul_one]
  have hcZ : c ∈ Subgroup.center Q := by
    have hzo : orderOf z = p := by
      refine orderOf_eq_prime ?_ hz1
      rw [hzc, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers c :=
      Subgroup.zpowers_le.2 (hzc ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i)
    have heq : Subgroup.zpowers z = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hco])
    have hcz : c ∈ Subgroup.zpowers z := by
      rw [heq]
      exact Subgroup.mem_zpowers c
    exact Subgroup.zpowers_le.2 hzZ hcz
  have hcent : Subgroup.centralizer ({c} : Set Q) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    exact Set.singleton_subset_iff.2 hcZ
  have hKnorm : Kb.Normal := by
    refine ⟨fun k hk q => ?_⟩
    have hqc : q ∈ Subgroup.centralizer ({c} : Set Q) := by rw [hcent]; trivial
    have hkc : k ∈ Subgroup.centralizer ({c} : Set Q) := hKbc hk
    have := hKbN.conj_mem ⟨k, hkc⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨q, hqc⟩
    exact Subgroup.mem_subgroupOf.1 this
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h.quasisimple hKnorm with htop | hle
  ·
    have hcK : c ∈ Kb := by rw [htop]; trivial
    have hcen : (⟨c, hcK⟩ : Kb) ∈ Subgroup.center Kb := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_center_iff.1 hcZ (k : Q))
    rw [hKz, Subgroup.mem_bot] at hcen
    exact hc1 (congrArg Subtype.val hcen)
  ·
    have : Nontrivial Kb := ⟨⟨⟨x, hxK⟩, 1, fun h1 => by
      have : x = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at hxo
      exact h.prime.ne_one hxo.symm⟩⟩
    have : Group.IsPerfect Kb := hKq.1
    refine Group.IsPerfect.not_isSolvable Kb (Group.isSolvable_of_comm fun a b => ?_)
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hle a.2) (b : Q)).symm

theorem Row8Conf.exists_image (h : Row8Conf p g Q Ē) :
    ∃ A : Subgroup (Q ⧸ Subgroup.center Q), IsElementaryAbelian p A ∧ Nat.card A = p ^ 2 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.elem
  refine ⟨Ē.map (QuotientGroup.mk' (Subgroup.center Q)), IsElementaryAbelian.map _, ?_⟩
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center Q)).comp Ē.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hz : (e : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 he
    have hmem : (e : Q) ∈ Ē ⊓ Subgroup.center Q := ⟨e.2, hz⟩
    rw [h.inf_center_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hrange : Ē.map (QuotientGroup.mk' (Subgroup.center Q)) =
      ((QuotientGroup.mk' (Subgroup.center Q)).comp Ē.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, ← h.card]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_le_of_isCyclic_elemAb {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (A : Subgroup Y) [IsCyclic A] (hA : IsElementaryAbelian p A) : Nat.card A ≤ p := by
  have hexp : Monoid.exponent ↥A ∣ p := IsElementaryAbelian.exponent_dvd_p p _
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd hp.pos hexp

end Conf

section Center

theorem center_eq_bot_of_multiplier {p : ℕ} (hp : p.Prime)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type}
    [Group Q] [Finite Q] (hqs : CFSG.IsQuasisimple Q) (hZ : IsPGroup p (Subgroup.center Q))
    {t : StatedLieTag} {n f : ℕ} (hm : Models.LieModel (Q ⧸ Subgroup.center Q) t n 2 f)
    (hcop : ¬ p ∣ Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f)) : Subgroup.center Q = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperfT, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hdvd := card_ker_dvd_card_hopfMultiplier hperfT hqs.1 (QuotientGroup.mk' (Subgroup.center Q))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
  rw [hcard, QuotientGroup.ker_mk'] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ
  rw [← Subgroup.card_eq_one]
  rw [hk] at hdvd ⊢
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd ((dvd_pow_self p hpos.ne').trans hdvd) hcop

end Center

end CFSG.RankThree.PartOne.Q1327T
