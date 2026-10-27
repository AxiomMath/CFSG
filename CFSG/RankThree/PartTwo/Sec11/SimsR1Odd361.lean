module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1OddLemmaP
public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Defs
public import CFSG.RankThree.PartTwo.Sec11.TwoStarProof

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSL)

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

section Tools

variable {G : Type} [Group G] [Finite G]

private theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  haveI := hsimple
  have : Group.IsSolvable (Q ⧸ Subgroup.center Q) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

private theorem exists_surjective_hom_of_cover {F : Type} [Group F] {L H : Subgroup G}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* F) (hHL : H ≤ L)
    (hcov : ∀ l ∈ L, ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) L, t * l ∈ H) :
    ∃ φ : H →* F, Function.Surjective φ := by
  refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp
    (Subgroup.inclusion hHL)), fun f => ?_⟩
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm f)
  obtain ⟨t, ⟨t', ht', rfl⟩, htl⟩ := hcov l l.2
  refine ⟨⟨(t' : G) * l, htl⟩, ?_⟩
  have h1 : Subgroup.inclusion hHL (⟨(t' : G) * l, htl⟩ : H) = t' * l := rfl
  have h2 : (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) t' = 1 :=
    (QuotientGroup.eq_one_iff t').mpr ht'
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [h1, map_mul, h2, one_mul]
  change e (QuotientGroup.mk' _ l) = f
  rw [QuotientGroup.mk'_apply, hl, MulEquiv.apply_symm_apply]

private theorem commutator_mem_theta_of_mem_thetaQuotCentralizer {L : Subgroup G} {q : G}
    (hq : q ∈ Sec4.thetaQuotCentralizer L) {l : G} (hl : l ∈ L) :
    q * l * q⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hq).2 l hl
  have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hl) _).mp h1
  have e1 : l * (l⁻¹ * (q * l * q⁻¹)) * l⁻¹ = q * l * q⁻¹ * l⁻¹ := by group
  rwa [e1] at h2

private theorem exists_mul_mem_centralizer_of_trivial_action {p : ℕ} [Fact p.Prime]
    {L X : Subgroup G} (hX : IsPGroup p X) (hXN : X ≤ Subgroup.normalizer (L : Set G))
    (hXtriv : ∀ q ∈ X, ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L)
    (hθ : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :
    ∀ l ∈ L, ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) L,
      t * l ∈ L ⊓ Subgroup.centralizer (X : Set G) := by
  set θ : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L
  have hθX : X ≤ Subgroup.normalizer (θ : Set G) :=
    hXN.trans (Sec6.normalizer_le_normalizer_theta L)
  have hXθ : X ⊓ θ = ⊥ := KFacts.inf_eq_bot_of_coprime hX hθ
  intro l hl
  have hcomm : ∀ y ∈ X, l * y * l⁻¹ * y⁻¹ ∈ θ := by
    intro y hy
    have h1 := hXtriv y hy l⁻¹ (L.inv_mem hl)
    have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hl) _).mp h1
    have e1 : l * (y * l⁻¹ * y⁻¹ * l⁻¹⁻¹) * l⁻¹ = l * y * l⁻¹ * y⁻¹ := by group
    rwa [e1] at h2
  have hlX : ∀ y ∈ X, l * y * l⁻¹ ∈ X ⊔ θ := by
    intro y hy
    have e1 : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm y hy)) (Subgroup.mem_sup_left hy)
  obtain ⟨t, ht, htN, htX⟩ := KFacts.exists_mul_mem_normalizer hX hθ hθX hlX
  refine ⟨t, ht, L.mul_mem (Sec6.theta_le L ht) hl, ?_⟩
  show t * l ∈ Subgroup.centralizer (X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : t * l * y * (t * l)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htN y).mp hy
  have h2 : t * l * y * (t * l)⁻¹ * y⁻¹ ∈ X := X.mul_mem h1 (X.inv_mem hy)
  have h3 : t * l * y * (t * l)⁻¹ * y⁻¹ ∈ θ := by
    have e1 : t * l * y * (t * l)⁻¹ * y⁻¹ =
        (t * l * y * (t * l)⁻¹ * (l * y * l⁻¹)⁻¹) * (l * y * l⁻¹ * y⁻¹) := by group
    rw [e1]
    exact θ.mul_mem (htX y hy) (hcomm y hy)
  have h4 : t * l * y * (t * l)⁻¹ * y⁻¹ ∈ X ⊓ θ := ⟨h2, h3⟩
  rw [hXθ, Subgroup.mem_bot] at h4
  have h5 : t * l * y * (t * l)⁻¹ = y := mul_inv_eq_one.mp h4
  calc y * (t * l) = (t * l * y * (t * l)⁻¹) * (t * l) := by rw [h5]
    _ = (t * l) * y := by group

end Tools

section Residue


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem eq_bot_of_normalized_by_cover (hB : KFacts.BlackburnRankTwo)
    (h : ResidueConfig G A c L a R Y d) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * 1)))
    {H Z : Subgroup G} (hHL : H ≤ L)
    (hcov : ∀ l ∈ L, ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) L, t * l ∈ H)
    (hZ : IsPGroup 2 Z) (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) : Z = ⊥ := by
  obtain ⟨φ, hφ⟩ := exists_surjective_hom_of_cover e hHL hcov
  obtain ⟨E, hE, hE3⟩ := exists_elemAbelian_of_surjective_L2Cube hB hp φ hφ
  refine eq_bot_of_normalized_by_elemAbelian h hp hZ (CFSG.Open.IsElemAbelian.map hE H.subtype)
    ?_ ?_
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hE3
  · rintro _ ⟨y, -, rfl⟩
    exact hHZ y.2

private theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  by_contra hlt
  have : p = 4 := by omega
  subst this
  exact absurd hp (by norm_num)

theorem pCore_two_centralizer_c_eq_bot_odd (hB : KFacts.BlackburnRankTwo) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hodd : IsL2OddCharOne L) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G)) = ⊥ := by
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  refine eq_bot_of_normalized_by_cover hB h (five_le_of_prime hp.out hp3) e (H := L) le_rfl
    (fun l hl => ⟨1, Subgroup.one_mem _, by simpa using hl⟩)
    (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) ?_
  intro l hl
  exact SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
    (TwoStarProof.le_centralizer_of_config h hl)

theorem odd_card_theta_L_odd (hB : KFacts.BlackburnRankTwo) (hDk : SimsR1L2CubeTwoLocal)
    (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hodd : IsL2OddCharOne L) : Odd (Nat.card (aschbacherSolvableCore 3 L)) := by
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L
  obtain ⟨P⟩ : Nonempty (Sylow 2 θ) := inferInstance
  set S : Subgroup G := (P : Subgroup θ).map θ.subtype
  have hS2 : IsPGroup 2 S := P.isPGroup'.map θ.subtype
  have hcov : ∀ l ∈ L, ∃ t ∈ θ, t * l ∈ L ⊓ Subgroup.normalizer (S : Set G) := by
    intro l hl
    obtain ⟨x, hx, hxl⟩ :=
      Sec6.exists_inv_mul_mem_normalizer_sylow P (Sec6.le_normalizer_theta L hl)
    exact ⟨x⁻¹, θ.inv_mem hx, L.mul_mem (L.inv_mem (Sec6.theta_le L hx)) hl, hxl⟩
  have hS1 : S = ⊥ := eq_bot_of_normalized_by_cover hB h (five_le_of_prime hp.out hp3) e
    inf_le_left hcov hS2 inf_le_right
  have hP1 : (P : Subgroup θ) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup θ) θ.subtype_injective).mp hS1
  have hPcard : Nat.card (P : Subgroup θ) = 1 := by rw [hP1]; exact Subgroup.card_bot
  have hn2 : ¬ 2 ∣ Nat.card θ := fun hd => by
    have := P.dvd_card_of_dvd_card hd
    rw [hPcard] at this
    omega
  have hcard : Nat.card θ = Nat.card (aschbacherSolvableCore 3 L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [← hcard]
  exact Nat.odd_iff.mpr (by omega)

theorem le_thetaQuotCentralizer_of_twoSubgroup_normalized_odd (hDk : SimsR1L2CubeTwoLocal)
    (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hodd : IsL2OddCharOne L) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXc : X ≤ Subgroup.centralizer ({c} : Set G)) {x : G} (hxA : x ∈ A)
    (hxB : x ∉ Subgroup.closure ({c, d} : Set G))
    (hKX : sec11K L x ≤ Subgroup.normalizer (X : Set G)) : X ≤ Sec4.thetaQuotCentralizer L := by
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  have hp5 := five_le_of_prime hp.out hp3
  have hXN : X ≤ Subgroup.normalizer (L : Set G) :=
    hXc.trans (TwoStarProof.centralizer_le_normalizer_of_config h45 h hT)
  have hA : A = Subgroup.closure {c, a, d} := by rw [← h.closure_eq, Set.pair_comm]
  obtain ⟨hxN, hx3, -, hQ, -⟩ :=
    basic_facts_of_conj h45 (h.toSec11Std hT) h.inf_eq_zpowers hA hxA hxB
  have hKb : (kMap L x).range =
      (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) :=
    (range_kMap_eq hxN hx3 hQ.1).trans (range_cMap hxN hx3)
  set N := Subgroup.normalizer (L : Set G)
  set ψ := TwoStarProof.autHom L with hψdef
  set Qh : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    (X.subgroupOf N).map ψ
  have hQh2 : IsPGroup 2 Qh := (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm).map ψ
  have hnorm : ∀ s ∈ (kMap L x).range, MulAut.conj s ∈ Subgroup.normalizer (Qh : Set _) := by
    rintro _ ⟨k, rfl⟩
    have hkL : (k : G) ∈ L := sec11K_le L x k.2
    have hkN : (k : G) ∈ N := Subgroup.le_normalizer hkL
    have hconj : MulAut.conj (kMap L x k) = ψ ⟨k, hkN⟩ := by
      rw [hψdef, TwoStarProof.autHom_of_mem hkN hkL]
      rfl
    rw [hconj]
    have hkX : (⟨k, hkN⟩ : N) ∈ Subgroup.normalizer ((X.subgroupOf N : Subgroup N) : Set N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp (hKX k.2) (y : G)
    exact Subgroup.le_normalizer_map ψ ⟨_, hkX, rfl⟩
  have hψ : ∀ q (hq : q ∈ X), ψ ⟨q, hXN hq⟩ = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hq, hq1⟩ := hcon
    have hne : Qh ≠ ⊥ := by
      intro hbot
      have hmem : ψ ⟨q, hXN hq⟩ ∈ Qh := ⟨⟨q, hXN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hq1 hmem
    have hsolv := hDk p hp5 (L ⧸ aschbacherSolvableCore 3 L) ⟨e⟩ Qh hQh2 hne _ hnorm
    rw [hKb] at hsolv
    exact not_isSolvable_of_isQuasisimple hQ hsolv
  intro q hq
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hXN hq, fun l hl => ?_⟩
  have h1 := TwoStarProof.commutator_mem_theta_of_autHom_eq_one (hXN hq) (hψ q hq) hl
  have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L (L.inv_mem hl)) _).mp h1
  have e1 : l⁻¹ * (q * l * q⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (q * l * q⁻¹) := by group
  rwa [e1] at h2

theorem eq_bot_of_twoSubgroup_normalized_odd (hB : KFacts.BlackburnRankTwo)
    (hDk : SimsR1L2CubeTwoLocal) (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) (hodd : IsL2OddCharOne L) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXc : X ≤ Subgroup.centralizer ({c} : Set G)) {x : G} (hxA : x ∈ A)
    (hxB : x ∉ Subgroup.closure ({c, d} : Set G))
    (hKX : sec11K L x ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  have hθodd := odd_card_theta_L_odd hB hDk h45 h hT hodd
  have hX1 := le_thetaQuotCentralizer_of_twoSubgroup_normalized_odd hDk h45 h hT hodd hX hXc hxA
    hxB hKX
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ2 : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hθodd
    omega
  have hcov := exists_mul_mem_centralizer_of_trivial_action hX
    (fun q hq => (Sec6.mem_thetaQuotCentralizer_iff.mp (hX1 hq)).1)
    (fun q hq l hl => commutator_mem_theta_of_mem_thetaQuotCentralizer (hX1 hq) hl) hθ2
  exact eq_bot_of_normalized_by_cover hB h (five_le_of_prime hp.out hp3) e inf_le_left hcov hX
    (fun w hw => Subgroup.centralizer_le_normalizer (X : Set G) hw.2)

end Residue

end CFSG.RankThree.PartTwo.Sec11.SimsR1
