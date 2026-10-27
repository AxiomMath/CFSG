module

public import CFSG.Quasithin.H13.NQTermTIFourWitness
public import CFSG.Quasithin.SteinbergCCConjugateEscape
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

theorem card_le_four_mul_card_inf_pCore {G : Type*} [Group G] [Finite G] {H E : Subgroup G}
    (hm2 : CFSG.pRank 2 (H ⧸ CFSG.pCore 2 H) ≤ 2) (hEH : E ≤ H)
    (hE : CFSG.IsElementaryAbelian 2 E) :
    Nat.card E ≤ 4 * Nat.card ↥(E ⊓ (CFSG.pCore 2 H).map H.subtype) := by
  classical
  set φ : E →* H ⧸ CFSG.pCore 2 H :=
    (QuotientGroup.mk' (CFSG.pCore 2 H)).comp (Subgroup.inclusion hEH)
  have h1 : Nat.card E = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hE2 : ∀ x : E, x ^ 2 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (x : G) x.2)
  have hEc : ∀ x y : E, x * y = y * x := fun x y => hE.toIsMulCommutative.is_comm.comm x y
  have : IsMulCommutative φ.range := ⟨⟨fun a b => by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : H ⧸ CFSG.pCore 2 H) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, hEc]⟩⟩
  have hR : CFSG.IsElementaryAbelian 2 φ.range :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      obtain ⟨x, hx⟩ := a.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, ← map_pow, hE2, map_one]⟩
  obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 φ.range).exists_card_eq
  have hk2 : k ≤ 2 := (CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two φ.range hR hk).trans hm2
  have h2 : Nat.card φ.range ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have h3 : Nat.card φ.ker = Nat.card ↥(E ⊓ (CFSG.pCore 2 H).map H.subtype) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, ⟨⟨x.1, hEH x.1.2⟩,
          (QuotientGroup.eq_one_iff (Subgroup.inclusion hEH x.1)).mp (MonoidHom.mem_ker.mp x.2),
          rfl⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, MonoidHom.mem_ker.mpr ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    obtain ⟨-, ⟨z, hz, hzy⟩⟩ := Subgroup.mem_inf.mp y.2
    change ((⟨y.1, _⟩ : H) : H ⧸ CFSG.pCore 2 H) = 1
    rw [QuotientGroup.eq_one_iff]
    have hzy' : z = ⟨y.1, hEH (Subgroup.mem_inf.mp y.2).1⟩ := Subtype.ext hzy
    rw [← hzy']
    exact hz
  rw [h1, h3]
  exact Nat.mul_le_mul h2 le_rfl

variable {G : Type} [Group G] [Finite G]

theorem nq_terminal_irreducible_four_witness {T L M : Subgroup G} (h : QTNQ T L M)
    (h16 : 16 ≤ Nat.card (qtnqU L M))
    (hirr : ∀ W : Subgroup G, W ≤ qtnqU L M → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W = ⊥ ∨ W = qtnqU L M)
    (hTI : ∀ x : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) x = ⊥ ∨
      CFSG.conjugate (qtnqU L M) x = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H Y : Subgroup G} (hTH : T ≤ H) (hYH : Y ≤ H) (hYn : (Y.subgroupOf H).Normal)
    (hYp : Group.IsPerfect Y) (hHY : IsPGroup 2 (H ⧸ Y.subgroupOf H))
    (hsimple : IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y))
    (hnab : ∃ a b : Y ⧸ CFSG.pCore 2 Y, a * b ≠ b * a)
    (hYM : ¬ Y ≤ M) (hm2 : CFSG.pRank 2 (H ⧸ CFSG.pCore 2 H) ≤ 2) :
    ∃ y ∈ Y, ∃ B : Subgroup G, B ≤ CFSG.conjugate (qtnqU L M) y ⊓ M ∧
      ¬ CFSG.conjugate (qtnqU L M) y ≤ M ∧ CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧
      ∀ b ∈ B, (∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype) → b = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := qtnqU L M with hUdef
  obtain ⟨-, -, -, -, ⟨hU1, hUM, hUn, hUel⟩, -⟩ :=
    nonquasisimple_normalizer_internal_module_properties h
  have hUp : IsPGroup 2 U := CFSG.IsElementaryAbelian.isPGroup 2 U
  have hMN : M ≤ normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  have hNU : normalizer (U : Set G) = M := h.max_two_local.2 _ ⟨U, hU1, hUp, rfl⟩ hMN
  have hTle : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ normalizer (P : Set G) → P ≤ T := by
    intro P hP hTP
    have hsup := hP.to_sup_of_normal_left' h.sylow.1 hTP
    have heq := (h.sylow.1.toSylow h.sylow.2).is_maximal' hsup le_sup_right
    exact le_sup_left.trans heq.le
  set Q := (CFSG.pCore 2 H).map H.subtype with hQdef
  have hQp : IsPGroup 2 Q := (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype
  have hHQ : H ≤ normalizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ hq' _, rfl⟩
    · rintro ⟨q', hq', hqq⟩
      refine ⟨⟨x, hx⟩⁻¹ * q' * ⟨x, hx⟩⁻¹⁻¹,
        (CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ hq' _, ?_⟩
      change x⁻¹ * (q' : G) * x⁻¹⁻¹ = q
      rw [show (q' : G) = x * q * x⁻¹ from hqq]
      group
  have hQT : Q ≤ T := hTle Q hQp (hTH.trans hHQ)
  have hQM : Q ≤ M := hQT.trans h.t_le
  have hUT : U ≤ T := hTle U hUp (h.t_le.trans hMN)
  have hcard : ∀ x : G, Nat.card (CFSG.conjugate U x) = Nat.card U := fun x =>
    Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have hbig : ∀ x : G, CFSG.conjugate U x ≤ H → 4 ≤ Nat.card ↥(CFSG.conjugate U x ⊓ Q) := by
    intro x hx
    have h1 : Nat.card (CFSG.conjugate U x) ≤ 4 * Nat.card ↥(CFSG.conjugate U x ⊓ Q) :=
      card_le_four_mul_card_inf_pCore hm2 hx (CFSG.IsElementaryAbelian.map _)
    rw [hcard] at h1
    omega
  have hconjH : ∀ x ∈ H, CFSG.conjugate U x ≤ H := fun x hx =>
    CFSG.GroupTheory.conjugate_le_of_mem (hUT.trans hTH) hx
  obtain ⟨g, hgT, hgQ⟩ : ∃ g : G, CFSG.conjugate U g ≤ T ∧ ¬ CFSG.conjugate U g ≤ Q := by
    by_contra hall
    push Not at hall
    apply hYM
    refine (hYH.trans ?_).trans hW
    set W := (sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate U g = X) ∧ X ≤ T} :
      Subgroup G)
    have hmapW : ∀ y ∈ H, W.map (MulAut.conj y).toMonoidHom ≤ W := by
      intro y hy
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun X hX => ?_
      obtain ⟨⟨x, rfl⟩, hXT⟩ := hX
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup ⟨⟨x * y⁻¹, ?_⟩, ?_⟩
      · show U.map (MulAut.conj (x * y⁻¹)⁻¹).toMonoidHom =
          (U.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom
        rw [Subgroup.map_map, mul_inv_rev, inv_inv, map_mul]
        rfl
      · calc (CFSG.conjugate U x).map (MulAut.conj y).toMonoidHom
            ≤ Q.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono (hall x hXT)
          _ = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hy)
          _ ≤ T := hQT
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hmapW y hy) fun w hw => ?_
    refine ⟨y⁻¹ * w * y, ?_, ?_⟩
    · have h1 : (MulAut.conj y⁻¹).toMonoidHom w ∈ W :=
        hmapW y⁻¹ (inv_mem hy) ⟨w, hw, rfl⟩
      simpa [MulAut.conj_apply] using h1
    · show y * (y⁻¹ * w * y) * y⁻¹ = w
      group
  have hUQ : ¬ U ≤ Q := by
    intro hUQ
    have hA₀H : CFSG.conjugate U g ≤ H := hgT.trans hTH
    have hA₀p : IsPGroup 2 (CFSG.conjugate U g) := hUp.map _
    obtain ⟨y, hyY, hyM⟩ := (SteinbergCC.perfect_two_extension_conjugate_escape hYH hYn hYp hHY
      hsimple hnab hA₀H hA₀p hgQ).2 hYM
    rw [CFSG.GroupTheory.conjugate_conjugate] at hyM
    have hA₁H : CFSG.conjugate U (g * y) ≤ H := by
      rw [← CFSG.GroupTheory.conjugate_conjugate]
      exact CFSG.GroupTheory.conjugate_le_of_mem hA₀H (hYH hyY)
    have hA₁p : IsPGroup 2 (CFSG.conjugate U (g * y)) := hUp.map _
    have hne : CFSG.conjugate U (g * y) ≠ U := fun he => hyM (by rw [he]; exact hUM)
    have hpg : IsPGroup 2 (U ⊔ CFSG.conjugate U (g * y) : Subgroup G) :=
      (hQp.to_sup_of_normal_left' hA₁p (hA₁H.trans hHQ)).to_le (sup_le_sup_right hUQ _)
    have hnorm : CFSG.conjugate U (g * y) ⊓ normalizer (U : Set G) ≠ ⊥ := by
      intro hbot
      have h4 : 4 ≤ Nat.card ↥(CFSG.conjugate U (g * y) ⊓ Q) := hbig _ hA₁H
      have hle : CFSG.conjugate U (g * y) ⊓ Q ≤ CFSG.conjugate U (g * y) ⊓
          normalizer (U : Set G) := inf_le_inf_left _ (hNU ▸ hQM)
      rw [hbot, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at h4
      omega
    have hcomm := (CFSG.Quasithin.SteinbergBM.nq_elementary_TI_pair_commutation hUel hTI hne).2
      hpg hnorm
    apply hyM
    rw [← hNU]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨y, hyY, hyM⟩ := (SteinbergCC.perfect_two_extension_conjugate_escape hYH hYn hYp hHY
    hsimple hnab (hUT.trans hTH) hUp hUQ).2 hYM
  have h4 : 4 ≤ Nat.card ↥(CFSG.conjugate U y ⊓ M) :=
    (hbig y (hconjH y (hYH hyY))).trans
      (Subgroup.card_le_of_le (inf_le_inf_left _ hQM))
  obtain ⟨B, hB, hBe, hB4, hBf⟩ := nq_irreducible_TI_intersection_four_witness h hirr hTI y hyM h4
  exact ⟨y, hyY, B, hB, hyM, hBe, hB4, hBf⟩

end CFSG.Quasithin.H13.NQTerm
