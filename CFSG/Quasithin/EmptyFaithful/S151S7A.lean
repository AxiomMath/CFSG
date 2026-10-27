module

public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151T6

public section

namespace CFSG.Quasithin.S151S7

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {Q : Type} [Group Q]

@[expose] def conjOnL (L : Subgroup G) (z : G) (hz : z ∈ Subgroup.normalizer (L : Set G)) : ↥L →* ↥L :=
  MonoidHom.mk' (fun l => ⟨z * (l : G) * z⁻¹, (Subgroup.mem_normalizer_iff.mp hz l).mp l.2⟩) (by
    intro a b
    apply Subtype.ext
    show z * ((a : G) * (b : G)) * z⁻¹ = (z * (a : G) * z⁻¹) * (z * (b : G) * z⁻¹)
    group)

theorem coe_conjOnL (L : Subgroup G) (z : G) (hz : z ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    ((conjOnL L z hz l : ↥L) : G) = z * (l : G) * z⁻¹ := rfl

theorem conjOnL_ker_le {L Kg : Subgroup G} (π : ↥L →* Q) (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G)) (z : G)
    (hz : z ∈ Subgroup.normalizer (L : Set G)) : π.ker ≤ (π.comp (conjOnL L z hz)).ker := by
  intro l hl
  rw [MonoidHom.mem_ker]
  have hl' : (l : G) ∈ Kg := by
    have h0 : l ∈ π.ker := hl
    rw [hKg] at h0
    exact h0
  have hz' : z ∈ Subgroup.normalizer (Kg : Set G) := hKgN hz
  have h1 : z * (l : G) * z⁻¹ ∈ Kg := (Subgroup.mem_normalizer_iff.mp hz' l).mp hl'
  have h2 : conjOnL L z hz l ∈ π.ker := by
    rw [hKg]
    exact h1
  exact h2

@[expose] noncomputable def inducedHom {L Kg : Subgroup G} (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G)) (z : G)
    (hz : z ∈ Subgroup.normalizer (L : Set G)) : Q →* Q :=
  MonoidHom.liftOfSurjective π hπ ⟨π.comp (conjOnL L z hz), conjOnL_ker_le π hKg hKgN z hz⟩

theorem inducedHom_apply {L Kg : Subgroup G} (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G)) (z : G)
    (hz : z ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    inducedHom π hπ hKg hKgN z hz (π l) = π (conjOnL L z hz l) := by
  simp [inducedHom]

theorem inducedHom_mul {L Kg : Subgroup G} (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G)) (z w : G)
    (hz : z ∈ Subgroup.normalizer (L : Set G)) (hw : w ∈ Subgroup.normalizer (L : Set G)) (q : Q) :
    inducedHom π hπ hKg hKgN (z * w) (mul_mem hz hw) q =
      inducedHom π hπ hKg hKgN z hz (inducedHom π hπ hKg hKgN w hw q) := by
  obtain ⟨l, rfl⟩ := hπ q
  rw [inducedHom_apply, inducedHom_apply, inducedHom_apply]
  congr 1
  apply Subtype.ext
  show z * w * (l : G) * (z * w)⁻¹ = z * (w * (l : G) * w⁻¹) * z⁻¹
  group

theorem inducedHom_one {L Kg : Subgroup G} (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G)) (q : Q) :
    inducedHom π hπ hKg hKgN 1 (one_mem _) q = q := by
  obtain ⟨l, rfl⟩ := hπ q
  rw [inducedHom_apply]
  congr 1
  apply Subtype.ext
  show 1 * (l : G) * (1 : G)⁻¹ = l
  group

theorem inducedHom_eq_of_centralizes {L Kg : Subgroup G} (π : ↥L →* Q)
    (hπ : Function.Surjective π) (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G)) (z : G)
    (hz : z ∈ Subgroup.normalizer (L : Set G)) (hc : z ∈ Subgroup.centralizer (L : Set G)) (q : Q) :
    inducedHom π hπ hKg hKgN z hz q = q := by
  obtain ⟨l, rfl⟩ := hπ q
  rw [inducedHom_apply]
  congr 1
  apply Subtype.ext
  show z * (l : G) * z⁻¹ = l
  rw [← Subgroup.mem_centralizer_iff.mp hc (l : G) l.2]
  group

theorem hom_into_ker_trivial_of_perfect {L : Subgroup G} (hperf : Group.IsPerfect ↥L) (π : ↥L →* Q)
    (hker : π.ker ≤ Subgroup.center ↥L) (κ : ↥L →* ↥L) (hκ : ∀ l, κ l ∈ π.ker) (l : ↥L) :
    κ l = 1 := by
  have hcomm : commutator ↥L ≤ κ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hκa : κ a ∈ Subgroup.center ↥L := hker (hκ a)
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hκa (κ b)).symm
  rw [hperf.commutator_eq_top, top_le_iff] at hcomm
  have : l ∈ κ.ker := by rw [hcomm]; exact Subgroup.mem_top l
  exact this

theorem centralizes_of_inducedHom_eq_id {L Kg : Subgroup G} (π : ↥L →* Q)
    (hπ : Function.Surjective π) (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G))
    (hκ : ∀ κ : ↥L →* ↥L, (∀ l, κ l ∈ π.ker) → ∀ l, κ l = 1) (hker : π.ker ≤ Subgroup.center ↥L)
    (z : G) (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hid : ∀ q, inducedHom π hπ hKg hKgN z hz q = q) :
    z ∈ Subgroup.centralizer (L : Set G) := by
  have hmem : ∀ l : ↥L, l⁻¹ * conjOnL L z hz l ∈ π.ker := by
    intro l
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← inducedHom_apply π hπ hKg hKgN z hz l, hid]
    exact inv_mul_cancel _
  let κ : ↥L →* ↥L := MonoidHom.mk' (fun l => l⁻¹ * conjOnL L z hz l) (by
    intro a b
    have hca : a⁻¹ * conjOnL L z hz a ∈ Subgroup.center ↥L := hker (hmem a)
    have h1 := Subgroup.mem_center_iff.mp hca b⁻¹
    calc (a * b)⁻¹ * conjOnL L z hz (a * b)
        = b⁻¹ * (a⁻¹ * conjOnL L z hz a) * conjOnL L z hz b := by rw [map_mul]; group
      _ = (a⁻¹ * conjOnL L z hz a) * b⁻¹ * conjOnL L z hz b := by rw [h1]
      _ = (a⁻¹ * conjOnL L z hz a) * (b⁻¹ * conjOnL L z hz b) := by group)
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have h1 : κ ⟨l, hl⟩ = 1 := hκ κ hmem ⟨l, hl⟩
  have h2 : (⟨l, hl⟩ : ↥L)⁻¹ * conjOnL L z hz ⟨l, hl⟩ = 1 := h1
  have h3 := congrArg Subtype.val h2
  have h4 : (l : G)⁻¹ * (z * l * z⁻¹) = 1 := h3
  have h5 : z * l * z⁻¹ = l := (inv_mul_eq_one.mp h4).symm
  calc l * z = (z * l * z⁻¹) * z := by rw [h5]
    _ = z * l := by group

theorem zl2_of_central_quotient {L S Kg : Subgroup G} (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hkerc : Subgroup.center ↥L ≤ π.ker)
    (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G))
    (hκ : ∀ κ : ↥L →* ↥L, (∀ l, κ l ∈ π.ker) → ∀ l, κ l = 1)
    (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hfix : AutFixSimple Q (((S ⊓ L).subgroupOf L).map π))
    (huniq : ∀ c d : Q, c ∈ centerOf (((S ⊓ L).subgroupOf L).map π) →
      d ∈ centerOf (((S ⊓ L).subgroupOf L).map π) →
      (∃ q, c * q * c⁻¹ ≠ q) → (∃ q, d * q * d⁻¹ ≠ q) →
      (∀ q, c ^ 2 * q * (c ^ 2)⁻¹ = q) → (∀ q, d ^ 2 * q * (d ^ 2)⁻¹ = q) →
      ∀ q, c * q * c⁻¹ = d * q * d⁻¹) :
    ZL2 S L := by
  intro a b haS hbS haC ha2 haZ hbC hb2 hbZ
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hSN haS
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hSN hbS
  have key : ∀ x : G, x ∈ S → ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
      x ∉ Subgroup.centralizer (L : Set G) → x ^ 2 ∈ Subgroup.centralizer (L : Set G) →
      (∀ c ∈ S, ⁅x, c⁆ ∈ Subgroup.centralizer (L : Set G)) →
      ∃ c ∈ centerOf (((S ⊓ L).subgroupOf L).map π),
        (∃ q, c * q * c⁻¹ ≠ q) ∧ (∀ q, c ^ 2 * q * (c ^ 2)⁻¹ = q) ∧
        ∀ q, inducedHom π hπ hKg hKgN x hx q = c * q * c⁻¹ := by
    intro x hxS hx hxC hx2 hxZ
    have hφφ : ∀ q, inducedHom π hπ hKg hKgN x hx (inducedHom π hπ hKg hKgN x hx q) = q := by
      intro q
      rw [← inducedHom_mul π hπ hKg hKgN x x hx hx q]
      have hxx : x * x ∈ Subgroup.centralizer (L : Set G) := by rw [← pow_two]; exact hx2
      exact inducedHom_eq_of_centralizes π hπ hKg hKgN (x * x) (mul_mem hx hx) hxx q
    have hφP : ∀ y ∈ ((S ⊓ L).subgroupOf L).map π, inducedHom π hπ hKg hKgN x hx y = y := by
      rintro _ ⟨y, hy, rfl⟩
      rw [inducedHom_apply]
      have hyS : (y : G) ∈ S := hy.1
      have hκC : ⁅x, (y : G)⁆ ∈ Subgroup.centralizer (L : Set G) := hxZ _ hyS
      have hcomm : ⁅x, (y : G)⁆ = (x * (y : G) * x⁻¹) * (y : G)⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      have hκL : ⁅x, (y : G)⁆ ∈ L := by
        have h1 : x * (y : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx y).mp y.2
        rw [hcomm]
        exact L.mul_mem h1 (L.inv_mem y.2)
      have hκcen : (⟨⁅x, (y : G)⁆, hκL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hκC (g : G) g.2)
      have hπκ : π ⟨⁅x, (y : G)⁆, hκL⟩ = 1 := hkerc hκcen
      have hyy : conjOnL L x hx y = ⟨⁅x, (y : G)⁆, hκL⟩ * y := by
        apply Subtype.ext
        show x * (y : G) * x⁻¹ = ⁅x, (y : G)⁆ * (y : G)
        rw [hcomm]
        group
      rw [hyy, map_mul, hπκ, one_mul]
    obtain ⟨c, hc, hcφ⟩ := hfix (inducedHom π hπ hKg hKgN x hx) hφφ hφP
    have hne : ∃ q, c * q * c⁻¹ ≠ q := by
      by_contra hcon
      apply hxC
      refine centralizes_of_inducedHom_eq_id π hπ hKg hKgN hκ hker x hx fun q => ?_
      rw [hcφ q]
      by_contra hq
      exact hcon ⟨q, hq⟩
    refine ⟨c, hc, hne, fun q => ?_, hcφ⟩
    have h1 := hφφ q
    rw [hcφ, hcφ] at h1
    calc c ^ 2 * q * (c ^ 2)⁻¹ = c * (c * q * c⁻¹) * c⁻¹ := by simp only [pow_two]; group
      _ = q := h1
  obtain ⟨ca, hca, hnea, hca2, hφa⟩ := key a haS haN haC ha2 haZ
  obtain ⟨cb, hcb, hneb, hcb2, hφb⟩ := key b hbS hbN hbC hb2 hbZ
  have heq : ∀ q, ca * q * ca⁻¹ = cb * q * cb⁻¹ := huniq ca cb hca hcb hnea hneb hca2 hcb2
  have hainv : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem haN
  have hab : a⁻¹ * b ∈ Subgroup.normalizer (L : Set G) := mul_mem hainv hbN
  have hid : ∀ q, inducedHom π hπ hKg hKgN (a⁻¹ * b) hab q = q := by
    intro q
    rw [inducedHom_mul π hπ hKg hKgN a⁻¹ b hainv hbN q, hφb q, ← heq q, ← hφa q]
    rw [← inducedHom_mul π hπ hKg hKgN a⁻¹ a hainv haN q]
    have h2 : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (L : Set G)), w = 1 →
        inducedHom π hπ hKg hKgN w hw q = q := by
      intro w hw hw1
      subst hw1
      exact inducedHom_one π hπ hKg hKgN q
    exact h2 _ _ (inv_mul_cancel a)
  exact centralizes_of_inducedHom_eq_id π hπ hKg hKgN hκ hker (a⁻¹ * b) hab hid

theorem conj_eq_of_unique_involution (P : Subgroup Q) (hcen : Subgroup.center Q = ⊥)
    (h : ∀ c d : Q, c ∈ centerOf P → d ∈ centerOf P → c ^ 2 = 1 → d ^ 2 = 1 → c ≠ 1 → d ≠ 1 → c = d) :
    ∀ c d : Q, c ∈ centerOf P → d ∈ centerOf P → (∃ q, c * q * c⁻¹ ≠ q) → (∃ q, d * q * d⁻¹ ≠ q) →
      (∀ q, c ^ 2 * q * (c ^ 2)⁻¹ = q) → (∀ q, d ^ 2 * q * (d ^ 2)⁻¹ = q) →
      ∀ q, c * q * c⁻¹ = d * q * d⁻¹ := by
  have hsq : ∀ c : Q, (∀ q, c ^ 2 * q * (c ^ 2)⁻¹ = q) → c ^ 2 = 1 := by
    intro c hc
    have hmem : c ^ 2 ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hc g
      calc g * c ^ 2 = (c ^ 2 * g * (c ^ 2)⁻¹) * c ^ 2 := by rw [this]
        _ = c ^ 2 * g := by group
    rw [hcen] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hne1 : ∀ c : Q, (∃ q, c * q * c⁻¹ ≠ q) → c ≠ 1 := by
    rintro c ⟨q, hq⟩ rfl
    exact hq (by group)
  intro c d hc hd hnc hnd hc2 hd2 q
  have := h c d hc hd (hsq c hc2) (hsq d hd2) (hne1 c hnc) (hne1 d hnd)
  rw [this]

end CFSG.Quasithin.S151S7

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15122ZPUniqueInv : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    ((IsPSU 3 3 1 Q ∨ IsTits Q ∨ Is3D4 2 1 Q) ∨ SporadicSix Q) →
      Subgroup.center Q = ⊥ ∧
        ∀ c d : Q, c ∈ centerOf P → d ∈ centerOf P → c ^ 2 = 1 → d ^ 2 = 1 → c ≠ 1 → d ≠ 1 → c = d

theorem sporadicSix_le_nine {X : Type} [Group X] (h : SporadicSix X) :
    IsSporadic .M11 X ∨ IsSporadic .M12 X ∨ IsSporadic .M22 X ∨ IsSporadic .M23 X ∨
      IsSporadic .M24 X ∨ IsSporadic .J2 X ∨ IsSporadic .HS X ∨ IsSporadic .He X ∨
      IsSporadic .Ru X := by
  rcases h with h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem input15122ThreeCZL2Loc_of_simple (hA : Input15120AutFixSimple) (hZ : Input15122ZPUniqueInv) :
    Input15122ThreeCZL2Loc := by
  intro G _ _ L S hC hS2 hSN hSyl
  let π : ↥L →* ↥L := MonoidHom.id ↥L
  have hπ : Function.Surjective π := Function.surjective_id
  have hk : π.ker = ⊥ := MonoidHom.ker_id
  have hP := sylow_map hSyl π hπ
  obtain ⟨hcen, huniq⟩ := hZ ↥L _ hP.1 hP.2 (Or.inl hC)
  have hbotN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := Subgroup.normalizer_eq_top _
  exact S151S7.zl2_of_central_quotient (Kg := ⊥) π hπ (by rw [hk]; exact bot_le)
    (by rw [hcen]; exact bot_le) (by rw [hk, Subgroup.bot_subgroupOf])
    (by rw [hbotN]; exact le_top)
    (fun κ hκ l => by
      have h := hκ l
      rw [hk] at h
      exact Subgroup.mem_bot.mp h)
    hSN (hA ↥L _ hP.1 hP.2 (Or.inl hC))
    (S151S7.conj_eq_of_unique_involution _ hcen huniq)

theorem input15122ThreeDZL2Loc_of_simple (hA : Input15120AutFixSimple) (hZ : Input15122ZPUniqueInv) :
    Input15122ThreeDZL2Loc := by
  intro G _ _ L S hq hZ2 hsix hS2 hSN hSyl
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hk : π.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hP := sylow_map hSyl π hπ
  have hcenL : Subgroup.center ↥L = CFSG.pCore 2 ↥L := zb_center_eq_pCore hq hZ2
  obtain ⟨hcen, huniq⟩ := hZ _ _ hP.1 hP.2 (Or.inr hsix)
  have hker : π.ker ≤ Subgroup.center ↥L := by
    rw [hk]
    exact pCore_le_center_of_quasisimple hq
  exact S151S7.zl2_of_central_quotient (Kg := pCoreOf 2 L) π hπ hker
    (le_of_eq (by rw [hk, hcenL])) (by rw [hk, pCoreOf_subgroupOf])
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    (fun κ hκ l => S151S7.hom_into_ker_trivial_of_perfect ⟨hq.1⟩ π hker κ hκ l)
    hSN (hA _ _ hP.1 hP.2 (Or.inr (sporadicSix_le_nine hsix)))
    (S151S7.conj_eq_of_unique_involution _ hcen huniq)

end CFSG.Quasithin
