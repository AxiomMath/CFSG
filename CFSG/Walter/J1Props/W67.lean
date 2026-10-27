module

public import CFSG.Walter.J1Props.Extra
public import CFSG.Walter.Final
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.J1Props

open CFSG.Open CFSG.Walter.W67
open scoped MatrixGroups

theorem nonempty_psl_mulEquiv_A5
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    (hq : p ^ f = 5) : Nonempty (PSL(2, GaloisField p f) ≃* alternatingGroup (Fin 5)) := by
  have hc : Nat.card (GaloisField p f) = 5 := by rw [GaloisField.card p f hf.ne', hq]
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hf, by rw [hc, hq]⟩
  have h60 : Nat.card PSL(2, GaloisField p f) = 60 := by
    rw [GorensteinWalter.psl2_card_formula _ hodd, hc]
    norm_num
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hc]; norm_num)
  exact CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h60

variable {L : Type} [Group L] [Finite L]

noncomputable def jankoHyp₀OfJRGroup
    (hL : JRGroup L) (hq : hL.q = 5) : JankoHyp₀ L where
  index_ne_two H hH := hL.index_ne_two H (Subgroup.normal_of_index_eq_two hH) hH
  abelian_sylow P := (hL.elementary_sylow P).toIsMulCommutative
  t := hL.J
  orderOf_t := hL.orderOf_J
  F := hL.K
  le_centralizer := hL.le_centralizer
  t_not_mem := hL.J_not_mem
  centralizer_eq := hL.centralizer_eq
  iso := hL.iso.trans (Classical.choice (nonempty_psl_mulEquiv_A5 hL.p_ne_two hL.f_pos hq))

theorem j1Prop_walterJ1 : J1Prop walterJ1 :=
  ⟨J1_simple, J1_card, fun _ _ hx hy => J1_isConj_involutions hx hy⟩

theorem card_sylow_of_seven {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 11 ∨ p = 19)
    (P : Sylow p walterJ1) : Nat.card (P : Subgroup walterJ1) = p := by
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
    rcases hp with rfl | rfl | rfl <;> simp
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj hp' P
  rw [hg, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ hp']

theorem card_normQuot_sylow {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 11 ∨ p = 19)
    (P : Sylow p walterJ1) :
    Nat.card (normQuot (P : Subgroup walterJ1)) = if p = 11 then 10 else 6 := by
  rcases hp with rfl | rfl | rfl
  · exact (J2_seven P).2
  · exact (J2_eleven P).2
  · exact (J2_nineteen P).2

theorem j2Prop_walterJ1 : J2Prop walterJ1 := by
  refine ⟨fun p _ hp2 P => J2_inverted hp2 P, fun p _ hp2 P t ht hP hPt => ?_,
    fun p _ P hp => ?_⟩
  · have h35 := J2_centralizer ht hp2 P hP hPt
    exact ⟨h35, J2_normalizer_two_part h35 P⟩
  · have hcyc := (isCyclic_normQuot (P : Subgroup walterJ1) (card_sylow_of_seven hp P)).1
    refine ⟨exists_zpowers_sup_eq _ hcyc, ?_⟩
    rw [Subgroup.index_eq_card]
    exact card_normQuot_sylow hp P

theorem j2Extra_walterJ1 : J2Extra walterJ1 :=
  ⟨fun _ _ hp2 P => card_sylow_odd hp2 P, fun _ _ hp P => centralizer_sylow_eq hp P,
    fun _ hx1 hodd => isSolvable_centralizer hx1 hodd⟩

theorem j3Prop_walterJ1 : J3Prop walterJ1 := by
  refine ⟨J3_aut, fun E _ _ Z _ hZ _ hE ⟨e⟩ => ?_⟩
  set π := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : π.ker = Z := by
    ext x
    simp [π]
  rw [← hker]
  exact J3_multiplier π (e.surjective.comp (QuotientGroup.mk'_surjective Z)) (hker ▸ hZ) hE

theorem outCyclic_walterJ1 : OutCyclic walterJ1 :=
  ⟨1, fun β => by
    obtain ⟨g, hg⟩ := J3_aut β
    exact ⟨0, g, by rw [hg, zpow_zero, one_mul]⟩⟩

section Transport

variable {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')

theorem map_centralizer_equiv (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hy _ ⟨z, hz, rfl⟩
    have := congrArg e (hy z hz)
    simpa using this
  · intro hy z hz
    have := congrArg e.symm (hy (e z) ⟨z, hz, rfl⟩)
    simpa using this

theorem card_normQuot_map_equiv [Finite G] (P : Subgroup G) :
    Nat.card (normQuot (P.map e.toMonoidHom)) = Nat.card (normQuot P) := by
  have hN : Nat.card (Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G')) =
      Nat.card (Subgroup.normalizer (P : Set G)) := by
    rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective e.injective]
  have hC : Nat.card (Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G')) =
      Nat.card (Subgroup.centralizer (P : Set G)) := by
    rw [← map_centralizer_equiv, Subgroup.card_map_of_injective e.injective]
  have h2 := card_normalizer_eq_mul (P.map e.toMonoidHom)
  rw [hN, hC, card_normalizer_eq_mul P] at h2
  have hpos : 0 < Nat.card (Subgroup.centralizer (P : Set G)) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

@[expose] noncomputable def sylowMap [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Sylow p G' :=
  P.mapSurjective (f := e.toMonoidHom) e.surjective

theorem coe_sylowMap [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (sylowMap e P : Subgroup G') = P.map e.toMonoidHom := rfl

theorem card_sylowMap [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Nat.card (sylowMap e P : Subgroup G') = Nat.card (P : Subgroup G) := by
  rw [coe_sylowMap, Subgroup.card_map_of_injective e.injective]

end Transport

theorem jFacts_of_mulEquiv (e : L ≃* walterJ1) :
    J1Prop L ∧ J2Prop L ∧ J2Extra L ∧ J3Prop L ∧ OutCyclic L := by
  have hJ1 : J1Prop L := by
    have : IsSimpleGroup walterJ1 := J1_simple
    refine ⟨e.isSimpleGroup, by rw [Nat.card_congr e.toEquiv, J1_card], fun x y hx hy => ?_⟩
    have hc := J1_isConj_involutions (x := e x) (y := e y) (by rw [MulEquiv.orderOf_eq, hx])
      (by rw [MulEquiv.orderOf_eq, hy])
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
    simpa using hc
  have haut : ∀ φ : MulAut L, ∃ g : L, φ = MulAut.conj g := by
    intro φ
    obtain ⟨g, hg⟩ := J3_aut (MulAut.congr e φ)
    refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
    have := congrArg (fun ψ : MulAut walterJ1 => ψ (e x)) hg
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply] at this
    rw [this, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨hJ1, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨haut, ?_⟩, ?_⟩
  ·
    intro p _ hp2 P
    obtain ⟨x, hx, hxz⟩ := J2_inverted hp2 (sylowMap e P)
    refine ⟨e.symm x, by rw [MulEquiv.orderOf_eq, hx], fun z hz => e.injective ?_⟩
    simpa using hxz (e z) ⟨z, hz, rfl⟩
  ·
    intro p _ hp2 P t ht hP hPt
    have hP' : (sylowMap e P : Subgroup walterJ1) ≠ ⊥ := by
      rw [coe_sylowMap, Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
      exact hP
    have hPt' : (sylowMap e P : Subgroup walterJ1) ≤
        Subgroup.centralizer ({e t} : Set walterJ1) := by
      rintro _ ⟨z, hz, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp (hPt hz)
      change e z ∈ _
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
    have h35 := J2_centralizer (x := e t) (by rw [MulEquiv.orderOf_eq, ht]) hp2 _ hP' hPt'
    refine ⟨h35, ?_⟩
    have := J2_normalizer_two_part h35 (sylowMap e P)
    rwa [coe_sylowMap, ← Subgroup.map_equiv_normalizer_eq,
      Subgroup.card_map_of_injective e.injective] at this
  ·
    intro p _ P hp
    have hcard : Nat.card (P : Subgroup L) = p := by
      rw [← card_sylowMap e P, card_sylow_of_seven hp]
    refine ⟨exists_zpowers_sup_eq _ (isCyclic_normQuot (P : Subgroup L) hcard).1, ?_⟩
    rw [Subgroup.index_eq_card]
    change Nat.card (normQuot (P : Subgroup L)) = _
    rw [← card_normQuot_map_equiv e, ← coe_sylowMap]
    exact card_normQuot_sylow hp _
  ·
    intro p _ hp2 P
    rw [← card_sylowMap e P]
    exact card_sylow_odd hp2 _
  ·
    intro p _ hp P
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_centralizer_equiv, ← coe_sylowMap]
    exact centralizer_sylow_eq hp _
  ·
    intro x hx1 hodd
    have hex1 : e x ≠ 1 := by rwa [Ne, map_eq_one_iff _ e.injective]
    have h := isSolvable_centralizer hex1 (by rwa [MulEquiv.orderOf_eq])
    let f : Subgroup.centralizer ({x} : Set L) →* Subgroup.centralizer ({e x} : Set walterJ1) :=
      (e.toMonoidHom.comp (Subgroup.centralizer ({x} : Set L)).subtype).codRestrict _ fun y => by
        have := Subgroup.mem_centralizer_singleton_iff.mp y.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        change e y * e x = e x * e y
        rw [← map_mul, ← map_mul, this]
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab =>
      Subtype.ext (e.injective (congrArg Subtype.val hab))
  ·
    intro E _ _ Z _ hZ hodd hE ⟨e'⟩
    exact j3Prop_walterJ1.2 E Z hZ hodd hE ⟨e'.trans e⟩
  ·
    refine ⟨1, fun β => ?_⟩
    obtain ⟨g, hg⟩ := haut β
    exact ⟨0, g, by rw [hg, zpow_zero, one_mul]⟩

end CFSG.Walter.J1Props

namespace CFSG.Walter.W67

theorem jFacts_of : J1RecogHyp → JFacts := by
  intro hR L _ _ hL hq
  have h₀ := J1Props.jankoHyp₀OfJRGroup hL hq
  obtain ⟨e⟩ := hR L (h₀.toJankoHyp h₀.isSimpleGroup)
  exact J1Props.jFacts_of_mulEquiv e

theorem jFacts : JFacts := jFacts_of j1RecogHyp

end CFSG.Walter.W67
