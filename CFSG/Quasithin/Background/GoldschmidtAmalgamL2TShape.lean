module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TQY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Shapes

variable [Finite D] {x a a₁ a₂ w : D}

theorem isCentralProduct₂_conjClosure (g : Gen A B z V x a a₁ a₂) (hwK : w ∈ kerK B V)
    (hww : w * w = z) (hKw : kerK B V = Subgroup.zpowers w) :
    IsCentralProduct₂ ↥(conjClosure V B) (Multiplicative (ZMod 4)) (QuaternionGroup 2) := by
  have h : Hyp2 A B z V := g.hyp
  have hcycK : IsCyclic ↥(kerK B V) := by rw [hKw]; infer_instance
  obtain ⟨e₁⟩ : Nonempty (↥(kerK B V) ≃* Multiplicative (ZMod 4)) :=
    ⟨haveI := hcycK; mulEquivOfCyclicCardEq (by rw [h.card_kerK, card_multiplicative_zmod_four])⟩
  have hwU : ∀ u ∈ conjClosure V B, w * u = u * w := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hwK.2 u hu).symm
  have hwUmem : w ∈ conjClosure V B := h.kerK_le_U hwK
  have hz1 : z ≠ 1 := h.natural.z_ne
  have hii : (a * w) * (a * w) = z := g.quat_ii hwU hww
  have hjj : (a₁ * w) * (a₁ * w) = z := g.quat_jj hwU hww
  have hjij : (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = (a * w)⁻¹ := g.quat_jij hwU hww
  have hiU : a * w ∈ conjClosure V B := (conjClosure V B).mul_mem g.a_mem_U hwUmem
  have hjU : a₁ * w ∈ conjClosure V B := (conjClosure V B).mul_mem g.a₁_mem_U hwUmem
  have hi2 : ¬ (a * w) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hii]; exact hz1
  have hi4 : (a * w) ^ 2 ^ (1 + 1) = 1 := by
    have e : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [e, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hii, h.z_mul_z]
  have hiord : orderOf (a * w) = 2 ^ (1 + 1) := orderOf_eq_prime_pow hi2 hi4
  have hZi : Nat.card (Subgroup.zpowers (a * w)) = 2 * 2 := by
    rw [Nat.card_zpowers, hiord]; norm_num
  have hgen : ∀ y : ↥(Subgroup.zpowers (a * w)),
      y ∈ Subgroup.zpowers (⟨a * w, Subgroup.mem_zpowers _⟩ : ↥(Subgroup.zpowers (a * w))) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨n, Subtype.ext (by simp)⟩
  let eZ := zmodMulEquivOfGenerator hgen hZi
  let coords : Multiplicative (ZMod (2 * 2)) →* D :=
    (Subgroup.zpowers (a * w)).subtype.comp eZ.toMonoidHom
  have hcoords_zpow : ∀ n : ℤ, coords (Multiplicative.ofAdd (n : ZMod (2 * 2))) = (a * w) ^ n := by
    intro n
    have := zmodMulEquivOfGenerator_apply_ofAdd_intCast hgen hZi n
    simp only [coords, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    change ((zmodMulEquivOfGenerator hgen hZi (Multiplicative.ofAdd (n : ZMod (2 * 2))) :
      ↥(Subgroup.zpowers (a * w))) : D) = _
    rw [this]
    simp
  have hcoords_mem : ∀ c, coords c ∈ Subgroup.zpowers (a * w) := fun c => (eZ c).2
  have hcinj : Function.Injective coords := Subtype.val_injective.comp eZ.injective
  have hJnot : a₁ * w ∉ coords.range := by
    rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcoords_mem c)
    have hcomm : (a * w) * (a₁ * w) = (a₁ * w) * (a * w) := by
      rw [← hc, ← hn]
      exact ((Commute.refl (a * w)).zpow_right n).eq
    have h1 : (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = a * w := by
      rw [← hcomm]; group
    rw [h1] at hjij
    have h2 : (a * w) * (a * w) = 1 := by
      calc (a * w) * (a * w) = (a * w) * (a * w)⁻¹⁻¹ := by rw [inv_inv]
        _ = (a * w)⁻¹ * (a * w)⁻¹⁻¹ := by rw [← hjij]
        _ = 1 := by rw [inv_inv]; group
    rw [hii] at h2
    exact hz1 h2
  have hsquare : (a₁ * w) ^ 2 = coords (Multiplicative.ofAdd (((2 : ℕ) : ZMod (2 * 2)))) := by
    have e1 := hcoords_zpow 2
    have e2 : (((2 : ℤ) : ZMod (2 * 2))) = ((2 : ℕ) : ZMod (2 * 2)) := by simp
    rw [e2] at e1
    rw [e1, pow_two, hjj, zpow_two, hii]
  have hinversion : ∀ c, (a₁ * w) * coords c * (a₁ * w)⁻¹ = (coords c)⁻¹ := by
    intro c
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcoords_mem c)
    rw [← hn, ← conj_zpow, hjij, inv_zpow]
  let f : QuaternionGroup 2 →* D :=
    CFSG.DisconnectedInvolutionGraph.Helpers.quaternionCoordinateHom 2 coords (a₁ * w)
      hsquare hinversion
  have hty : ∀ p q : ZMod (2 * 2),
      coords (Multiplicative.ofAdd p) ≠ (a₁ * w) * coords (Multiplicative.ofAdd q) := by
    intro p q hpq
    apply hJnot
    have e : a₁ * w = coords (Multiplicative.ofAdd p) * (coords (Multiplicative.ofAdd q))⁻¹ := by
      rw [hpq]; group
    rw [e]
    exact coords.range.mul_mem ⟨_, rfl⟩ (coords.range.inv_mem ⟨_, rfl⟩)
  have hfinj : Function.Injective f := by
    intro p q hpq
    cases p with
    | a p =>
      cases q with
      | a q =>
        change coords (Multiplicative.ofAdd p) = coords (Multiplicative.ofAdd q) at hpq
        exact congrArg QuaternionGroup.a (congrArg Multiplicative.toAdd (hcinj hpq))
      | xa q => exact (hty p q hpq).elim
    | xa p =>
      cases q with
      | a q => exact (hty q p hpq.symm).elim
      | xa q =>
        change (a₁ * w) * coords (Multiplicative.ofAdd p) =
          (a₁ * w) * coords (Multiplicative.ofAdd q) at hpq
        exact congrArg QuaternionGroup.xa
          (congrArg Multiplicative.toAdd (hcinj (mul_left_cancel hpq)))
  have hIf : a * w ∈ f.range := by
    refine ⟨QuaternionGroup.a 1, ?_⟩
    change coords (Multiplicative.ofAdd (1 : ZMod (2 * 2))) = a * w
    have := hcoords_zpow 1
    simpa using this
  have hJf : a₁ * w ∈ f.range := by
    refine ⟨QuaternionGroup.xa 0, ?_⟩
    change (a₁ * w) * coords (Multiplicative.ofAdd (0 : ZMod (2 * 2))) = a₁ * w
    simp
  have hfU : f.range ≤ conjClosure V B := by
    rintro _ ⟨q, rfl⟩
    cases q with
    | a k =>
      change coords (Multiplicative.ofAdd k) ∈ conjClosure V B
      exact Subgroup.zpowers_le.mpr hiU (hcoords_mem _)
    | xa k =>
      change (a₁ * w) * coords (Multiplicative.ofAdd k) ∈ conjClosure V B
      exact (conjClosure V B).mul_mem hjU (Subgroup.zpowers_le.mpr hiU (hcoords_mem _))
  have hfcard : Nat.card f.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hKQ : kerK B V ≤ conjClosure V B := h.kerK_le_U
  have hBQ : f.range ≤ conjClosure V B := hfU
  have hc₀ : a * a₁ * a₂ ∈ kerK B V := by
    rw [h.kerK_eq_center_U]; exact g.c_mem_center
  have hwinv : w⁻¹ ∈ kerK B V := (kerK B V).inv_mem hwK
  have hgens : ∀ S : Subgroup D, a * w ∈ S → a₁ * w ∈ S → w ∈ S → a * a₁ * a₂ ∈ S →
      conjClosure V B ≤ S := by
    intro S hiS hjS hwS hcS
    have haS : a ∈ S := by
      have e : a = (a * w) * w⁻¹ := by group
      rw [e]; exact S.mul_mem hiS (S.inv_mem hwS)
    have ha₁S : a₁ ∈ S := by
      have e : a₁ = (a₁ * w) * w⁻¹ := by group
      rw [e]; exact S.mul_mem hjS (S.inv_mem hwS)
    have hzS : z ∈ S := by rw [← hww]; exact S.mul_mem hwS hwS
    have ha₂S : a₂ ∈ S := by
      have e : a₂ = a₁⁻¹ * a⁻¹ * (a * a₁ * a₂) := by group
      rw [e]; exact S.mul_mem (S.mul_mem (S.inv_mem ha₁S) (S.inv_mem haS)) hcS
    rw [g.U_eq_closure, Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht | ht <;> rw [ht] <;> assumption
  have hKB : kerK B V ⊔ f.range = conjClosure V B := by
    refine le_antisymm (sup_le hKQ hBQ) ?_
    exact hgens _ (Subgroup.mem_sup_right hIf) (Subgroup.mem_sup_right hJf)
      (Subgroup.mem_sup_left hwK) (Subgroup.mem_sup_left hc₀)
  have hKnotle : ¬ kerK B V ≤ f.range := by
    intro hle
    have hUle := hgens f.range hIf hJf (hle hwK) (hle hc₀)
    have := Subgroup.card_le_of_le hUle
    rw [h.card_U, hfcard] at this
    omega
  have hzKB : z ∈ kerK B V ⊓ f.range :=
    ⟨h.center_U_le_K h.z_mem_center_U, by rw [← hii]; exact f.range.mul_mem hIf hIf⟩
  have hKB2 : Nat.card ↥(kerK B V ⊓ f.range) = 2 := by
    have hdvd : Nat.card ↥(kerK B V ⊓ f.range) ∣ Nat.card ↥(kerK B V) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [h.card_kerK] at hdvd
    have hge : 2 ≤ Nat.card ↥(kerK B V ⊓ f.range) := by
      have hle : Subgroup.zpowers z ≤ kerK B V ⊓ f.range := Subgroup.zpowers_le.mpr hzKB
      have := Subgroup.card_le_of_le hle
      rwa [h.card_zpowers] at this
    have hne4 : Nat.card ↥(kerK B V ⊓ f.range) ≠ 4 := by
      intro h4
      apply hKnotle
      have e : kerK B V ⊓ f.range = kerK B V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, h.card_kerK])
      rw [← e]; exact inf_le_right
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hdvd
    generalize Nat.card ↥(kerK B V ⊓ f.range) = m at *
    interval_cases m <;> omega
  refine ⟨(kerK B V).subgroupOf (conjClosure V B), f.range.subgroupOf (conjClosure V B), ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hKQ hBQ, hKB, Subgroup.subgroupOf_self]
  · intro a' ha' b' hb'
    apply Subtype.ext
    have haK : (a' : D) ∈ kerK B V := ha'
    have hbU : (b' : D) ∈ conjClosure V B := hfU hb'
    exact (Subgroup.mem_centralizer_iff.mp haK.2 _ hbU).symm
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hKQ).trans e₁⟩
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hBQ).trans (MonoidHom.ofInjective hfinj).symm⟩
  · have e : (kerK B V).subgroupOf (conjClosure V B) ⊓ f.range.subgroupOf (conjClosure V B) =
        (kerK B V ⊓ f.range).subgroupOf (conjClosure V B) := (Subgroup.comap_inf _ _ _).symm
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKQ)).toEquiv]
    exact hKB2

theorem isCentralProduct₂_conjClosure_c (g : Gen A B z V x a a₁ a₂) :
    IsCentralProduct₂ ↥(conjClosure V B) (Multiplicative (ZMod 4)) (QuaternionGroup 2) :=
  isCentralProduct₂_conjClosure g (c_mem_kerK g) (c_sq g) (kerK_eq_zpowers_c g)

theorem nonempty_yGrp_mulEquiv (g : Gen A B z V x a a₁ a₂) (hT : Nat.card ↥(A ⊓ B) = 64) :
    Nonempty (↥(yGrp A B V) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have h : Hyp2 A B z V := g.hyp
  obtain ⟨y, hyA, hyT⟩ := h.exists_y
  obtain ⟨hY, -⟩ := yGrp_eq_sup g hT hyA hyT
  have hint : kerK B V ⊓ conjSub y (kerK B V) = ⊥ := h.K_inf_conj_eq_bot hyA hyT
  have hKK' := h.kerK_comm_conjSub hyA hyT
  have hcardK' : Nat.card ↥(conjSub y (kerK B V)) = 4 := by
    rw [card_conjSub]; exact h.card_kerK
  have hcycK : IsCyclic ↥(kerK B V) := by rw [kerK_eq_zpowers_c g]; infer_instance
  have hK'eq : conjSub y (kerK B V) = Subgroup.zpowers (y * (a * a₁ * a₂) * y⁻¹) := by
    rw [kerK_eq_zpowers_c g]
    unfold conjSub
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hcycK' : IsCyclic ↥(conjSub y (kerK B V)) := by rw [hK'eq]; infer_instance
  let e₁ : ↥(kerK B V) ≃* Multiplicative (ZMod 4) :=
    haveI := hcycK
    mulEquivOfCyclicCardEq (by rw [h.card_kerK, card_multiplicative_zmod_four])
  let e₂ : ↥(conjSub y (kerK B V)) ≃* Multiplicative (ZMod 4) :=
    haveI := hcycK'
    mulEquivOfCyclicCardEq (by rw [hcardK', card_multiplicative_zmod_four])
  obtain ⟨e⟩ := GoldAmN.nonempty_mulEquiv_prod_of_sup_eq (yGrp A B V) (kerK B V)
    (conjSub y (kerK B V)) K_le_yGrp (conjSub_K_le_yGrp hyA) hY.symm hKK' hint
  exact ⟨e.trans (e₁.prodCongr e₂)⟩

end Shapes

end GoldAmL2T

end F6

end CFSG.Quasithin
