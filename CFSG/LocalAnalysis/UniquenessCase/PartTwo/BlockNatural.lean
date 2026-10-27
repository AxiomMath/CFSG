module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkA
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.GroupTheory.SteinbergCBFTPSolvable
public import CFSG.Quasithin.Background.C126NatSL2
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

@[expose] def conjV {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (l : ↥L) (v : ↥V) : ↥V :=
  ⟨(l : G) * (v : G) * (l : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLV l.2) (v : G)).mp v.2⟩

structure Coordinates (L V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (n : ℕ) where
  K : Type
  fieldK : Field K
  finiteK : Finite K
  cardK : Nat.card K = 2 ^ n
  α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K
  α_surj : Function.Surjective α
  α_ker : α.ker = (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L
  E : Vtil (⊥ : Subgroup G) V hV ≃* Multiplicative (Fin 2 → K)
  β : ↥V →* Multiplicative (Fin 2 → K)
  β_bij : Function.Bijective β
  β_act : ∀ (l : ↥L) (v : ↥V),
    β (conjV hLV l v) =
      Multiplicative.ofAdd (((α l : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β v)))

attribute [instance] Coordinates.fieldK Coordinates.finiteK

instance Coordinates.charP_two {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ}
    (c : Coordinates L V hV hLV n) : CharP c.K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype c.K := Fintype.ofFinite c.K
  exact charP_of_card_eq_prime_pow (f := n) (by
    rw [Fintype.card_eq_nat_card]
    exact c.cardK)

theorem exists_coordinates {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (hnat : BinaryNaturalSL (barSub (⊥ : Subgroup G) V hV L) ⊤ ⊥ 2 n) :
    Nonempty (Coordinates L V hV hLV n) := by
  classical
  obtain ⟨K, hK, hKfin, hKcard, π, hπ⟩ := hnat
  letI : Field K := hK
  letI : Finite K := hKfin
  let H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) := barSub ⊥ V hV L
  let D : FFModel := FFModel.nat (StatedSL 2 K)
  let eH : ↥(StatedSL 2 K) ≃* ↥H :=
    MulEquiv.ofBijective π ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
  obtain ⟨E, hE⟩ := CFSG.Quasithin.G64.RealizesVia.exists_secEquiv (D := D) (H := H) rfl hπ
  let E' : Vtil (⊥ : Subgroup G) V hV ≃* Multiplicative (Fin 2 → K) :=
    E.trans (Subgroup.topEquiv (G := Multiplicative (Fin 2 → K)))
  have hLbot : L ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  have hLstab : L ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hLV hLbot
  let ψ : ↥L →* MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    (actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hLstab)
  let ρ : ↥L →* ↥H :=
    ψ.codRestrict H fun l =>
      actTil_mem_barSub (⊥ : Subgroup G) V hV l.2 (Subgroup.inclusion hLstab l).2
  have hρ_surj : Function.Surjective ρ := by
    intro h
    obtain ⟨g, hgL, hg⟩ := (mem_barSub (⊥ : Subgroup G) V hV L (h : MulAut _)).1 h.2
    refine ⟨⟨(g : G), hgL⟩, Subtype.ext ?_⟩
    show (actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hLstab ⟨(g : G), hgL⟩) :
      MulAut (Vtil (⊥ : Subgroup G) V hV)) = (h : MulAut _)
    rw [show (Subgroup.inclusion hLstab ⟨(g : G), hgL⟩ : stabTil (⊥ : Subgroup G) V) = g
      from Subtype.ext rfl, hg]
  let σ : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(StatedSL 2 K) :=
    specialLinearGroupEquivStatedSL 2 K
  let eSL : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    eH.symm.trans σ.symm
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K := eSL.toMonoidHom.comp ρ
  have hα_surj : Function.Surjective α := eSL.surjective.comp hρ_surj
  have hα_ker : α.ker = (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : ρ l = 1 := eSL.injective (by simpa [α] using h)
      have h2 : (actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hLstab l) :
          MulAut (Vtil (⊥ : Subgroup G) V hV)) = 1 := congrArg Subtype.val h1
      have h3 := (actTil_eq_one_iff (⊥ : Subgroup G) V hV
        (Subgroup.inclusion hLstab l)).1 h2
      refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h4 : (l : G) * v * (l : G)⁻¹ = v := by
        have := h3 v hv
        rw [Subgroup.mem_bot] at this
        exact mul_inv_eq_one.mp this
      calc v * (l : G) = ((l : G) * v * (l : G)⁻¹) * (l : G) := by rw [h4]
        _ = (l : G) * v := by group
    · rintro ⟨-, hc⟩
      show eSL (ρ l) = 1
      rw [MulEquiv.map_eq_one_iff]
      apply Subtype.ext
      change actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hLstab l) = 1
      rw [actTil_eq_one_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      have hc' := (Subgroup.mem_centralizer_iff.mp hc) v hv
      have h4 : (l : G) * v * (l : G)⁻¹ = v := by
        rw [← hc']
        group
      simp only [Subgroup.coe_inclusion]
      rw [h4]
      group
  let mkHom : ↥V →* IntMod V hV :=
    { toFun := IntMod.mk hV
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let β : ↥V →* Multiplicative (Fin 2 → K) :=
    E'.toMonoidHom.comp ((mkTil (⊥ : Subgroup G) V hV).comp mkHom)
  have hmk_inj : Function.Injective mkHom := by
    intro a b h
    exact IntMod.val_injective (congrArg IntMod.val h)
  have hmk_surj : Function.Surjective mkHom := by
    intro x
    exact ⟨⟨x.val, x.val_mem⟩, rfl⟩
  have hβ_bij : Function.Bijective β :=
    ⟨E'.injective.comp ((mkTil_bot_injective hV).comp hmk_inj),
      E'.surjective.comp ((mkTil_surjective (⊥ : Subgroup G) V hV).comp hmk_surj)⟩
  have hβ_act : ∀ (l : ↥L) (v : ↥V),
      β (conjV hLV l v) =
        Multiplicative.ofAdd (((α l : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β v))) := by
    intro l v
    have hγ : σ (α l) = eH.symm (ρ l) := by
      change σ (σ.symm (eH.symm (ρ l))) = eH.symm (ρ l)
      rw [MulEquiv.apply_symm_apply]
    have hπγ : π (σ (α l)) = ρ l := by
      rw [hγ]
      exact eH.apply_symm_apply (ρ l)
    have hmt : mkTil (⊥ : Subgroup G) V hV (mkHom (conjV hLV l v)) =
        actTil (⊥ : Subgroup G) V hV (Subgroup.inclusion hLstab l)
          (mkTil (⊥ : Subgroup G) V hV (mkHom v)) := by
      rw [actTil_mk]
      apply congrArg (mkTil (⊥ : Subgroup G) V hV)
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl
    change E' (mkTil (⊥ : Subgroup G) V hV (mkHom (conjV hLV l v))) =
      Multiplicative.ofAdd (((α l : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β v)))
    rw [hmt]
    have htop : ∀ z : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))),
        (Subgroup.topEquiv z : Multiplicative (Fin 2 → K)) = (z : Multiplicative _) := fun z => rfl
    have hEapply : (Subgroup.topEquiv (E (((ρ l : ↥H) : MulAut
        (Vtil (⊥ : Subgroup G) V hV)) (mkTil (⊥ : Subgroup G) V hV (mkHom v)))) :
          Multiplicative (Fin 2 → K)) =
        Multiplicative.ofAdd (((σ (α l) : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd
            (Subgroup.topEquiv (E (mkTil (⊥ : Subgroup G) V hV (mkHom v)))))) := by
      have h := hE (σ (α l)) (mkTil (⊥ : Subgroup G) V hV (mkHom v))
      rw [hπγ] at h
      simpa [D, FFModel.nat, natAct, htop] using h
    change (Subgroup.topEquiv (E (((ρ l : ↥H) : MulAut
      (Vtil (⊥ : Subgroup G) V hV)) (mkTil (⊥ : Subgroup G) V hV (mkHom v)))) :
        Multiplicative (Fin 2 → K)) = _
    rw [hEapply, specialLinearGroupEquivStatedSL_coe]
    rfl
  exact ⟨K, hK, hKfin, hKcard, α, hα_surj, hα_ker, E', β, hβ_bij, hβ_act⟩

theorem Coordinates.irreducible {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    {W : Subgroup G} (hWV : W ≤ V) (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ ∨ W = V := by
  let W' : AddSubgroup (Fin 2 → c.K) :=
    { carrier := {w | ∃ u : ↥V, (u : G) ∈ W ∧ Multiplicative.toAdd (c.β u) = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', W.mul_mem hu hu', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, W.inv_mem hu, by rw [map_inv, toAdd_inv]⟩ }
  have hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) c.K, ∀ w ∈ W',
      (g : Matrix (Fin 2) (Fin 2) c.K).mulVec w ∈ W' := by
    rintro g _ ⟨u, hu, rfl⟩
    obtain ⟨l, rfl⟩ := c.α_surj g
    refine ⟨conjV hLV l u, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hLW l.2) (u : G)).mp hu
    · rw [c.β_act l u]
      rfl
  rcases CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.eq_bot_or_eq_top_of_invariant W' hinv with h' | h'
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxW' : Multiplicative.toAdd (c.β ⟨x, hWV hx⟩) ∈ W' := ⟨⟨x, hWV hx⟩, hx, rfl⟩
    rw [h', AddSubgroup.mem_bot] at hxW'
    have h1 : c.β ⟨x, hWV hx⟩ = c.β 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective (by simpa using hxW')
    have h2 := c.β_bij.1 h1
    simpa using congrArg Subtype.val h2
  · right
    refine le_antisymm hWV fun v hv => ?_
    have hvW' : Multiplicative.toAdd (c.β ⟨v, hv⟩) ∈ W' := h' ▸ AddSubgroup.mem_top _
    obtain ⟨u, hu, hue⟩ := hvW'
    have h2 : u = ⟨v, hv⟩ := c.β_bij.1 (Multiplicative.toAdd.injective hue)
    have hv' : v = (u : G) := by rw [h2]
    rw [hv']
    exact hu

theorem Coordinates.V_ne_bot {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n) :
    V ≠ ⊥ := by
  intro hbot
  obtain ⟨u, hu⟩ := c.β_bij.2 (Multiplicative.ofAdd (Pi.single (0 : Fin 2) 1))
  have hu1 : u = 1 := Subtype.ext (by
    have : (u : G) ∈ (⊥ : Subgroup G) := hbot ▸ u.2
    exact Subgroup.mem_bot.1 this)
  have hne : (Multiplicative.ofAdd (Pi.single (0 : Fin 2) 1) : Multiplicative (Fin 2 → c.K)) ≠ 1 := by
    intro h
    have h0 : (Pi.single (0 : Fin 2) (1 : c.K)) = (0 : Fin 2 → c.K) := by
      simpa using congrArg Multiplicative.toAdd h
    have h1 := congrFun h0 (0 : Fin 2)
    simpa using h1
  rw [hu1, map_one] at hu
  exact hne hu.symm

theorem Coordinates.two_dvd_card {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n) :
    2 ∣ Nat.card ↥V := by
  have hVp : IsPGroup 2 ↥V := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV
  obtain ⟨m, hm⟩ := hVp.exists_card_eq
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero] at hm
    exact c.V_ne_bot (Subgroup.card_eq_one.mp hm)
  rw [hm]
  exact dvd_pow_self 2 hm0

theorem Coordinates.blockQ_eq {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    blockQ L = L ⊓ Subgroup.centralizer (V : Set G) := by
  classical
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let C : Subgroup G := L ⊓ Subgroup.centralizer (V : Set G)
  have hQN : L ≤ Subgroup.normalizer ((Q.map L.subtype : Subgroup G) : Set G) := by
    rw [← CFSG.AGLEmbedding.NoXBlock.blockQ_eq_map L]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  letI : MulAction ↥Q ↥V :=
    { smul := fun q v => conjV hLV (q : ↥L) v
      one_smul := fun v => by
        apply Subtype.ext
        change ((1 : ↥Q) : G) * (v : G) * (((1 : ↥Q) : G))⁻¹ = (v : G)
        simp
      mul_smul := fun q r v => by
        apply Subtype.ext
        change ((q * r : ↥Q) : G) * (v : G) * (((q * r : ↥Q) : G))⁻¹ =
          (q : G) * ((r : G) * (v : G) * (r : G)⁻¹) * (q : G)⁻¹
        simp only [Subgroup.coe_mul]
        group }
  have hQ2 : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  obtain ⟨v, hv, hv1⟩ := hQ2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥V)
    c.two_dvd_card (a := 1) (fun q => by
      apply Subtype.ext
      show (q : G) * (1 : G) * (q : G)⁻¹ = (1 : G)
      simp)
  have hvC : (v : G) ∈ Subgroup.centralizer ((Q.map L.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hx
    have hvq := (MulAction.mem_fixedPoints.mp hv) ⟨q, hq⟩
    have hconj : (q : G) * (v : G) * (q : G)⁻¹ = (v : G) := congrArg Subtype.val hvq
    calc (q : G) * (v : G) = ((q : G) * (v : G) * (q : G)⁻¹) * (q : G) := by group
      _ = (v : G) * (q : G) := by rw [hconj]
  let W : Subgroup G := V ⊓ Subgroup.centralizer ((Q.map L.subtype : Subgroup G) : Set G)
  have hWle : W ≤ V := inf_le_left
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hvW : (v : G) ∈ W := ⟨v.2, hvC⟩
    rw [hbot, Subgroup.mem_bot] at hvW
    exact hv1 (Subtype.ext hvW).symm
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine CFSG.Quasithin.B2F.le_normalizer_inf hLV ?_
    exact hQN.trans (CFSG.Quasithin.B2F.normalizer_le_normalizer_centralizer _)
  have hW : W = ⊥ ∨ W = V := c.irreducible hWle hLW
  rcases hW with hbot | htop
  · exact absurd hbot hWne
  · refine le_antisymm ?_ ?_
    · intro x hx
      have hxQ : x ∈ (Q.map L.subtype : Subgroup G) := by
        rwa [CFSG.AGLEmbedding.NoXBlock.blockQ_eq_map L] at hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hxQ
      refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hCV : V ≤ Subgroup.centralizer ((Q.map L.subtype : Subgroup G) : Set G) := by
        rw [← htop]
        exact inf_le_right
      exact ((Subgroup.mem_centralizer_iff.mp (hCV hw)) (q : G) ⟨q, hq, rfl⟩).symm
    · refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 C L inf_le_left ?_ hC
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
        (CFSG.Quasithin.B2F.le_normalizer_inf (Subgroup.le_normalizer)
          (CFSG.Quasithin.B2F.le_normalizer_centralizer hLV))

theorem Coordinates.not_central {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n) :
    ¬ L ≤ Subgroup.centralizer (V : Set G) := by
  intro hLC
  obtain ⟨l, hl⟩ := c.α_surj (⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ :
    Matrix.SpecialLinearGroup (Fin 2) c.K)
  obtain ⟨v, hv⟩ := c.β_bij.2 (Multiplicative.ofAdd (Pi.single (1 : Fin 2) 1))
  have hconj : conjV hLV l v = v := by
    apply Subtype.ext
    show (l : G) * (v : G) * (l : G)⁻¹ = (v : G)
    rw [← (Subgroup.mem_centralizer_iff.mp (hLC l.2) v v.2)]
    group
  have h1 := c.β_act l v
  rw [hconj, hv, hl] at h1
  have h2 : (Pi.single (1 : Fin 2) (1 : c.K)) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) c.K).mulVec (Pi.single (1 : Fin 2) 1) :=
    Multiplicative.ofAdd.injective (by simpa using h1)
  have h3 := congrFun h2 (0 : Fin 2)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h3

theorem Coordinates.commutator_eq {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n) :
    ⁅V, L⁆ = V := by
  have hle : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have h1 : l * v⁻¹ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
    have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h1
  have hN : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hLV Subgroup.le_normalizer
  rcases c.irreducible hle hN with h' | h'
  · exfalso
    apply c.not_central
    have hbot : ⁅V, L⁆ = ⊥ := h'
    have hVc : V ≤ Subgroup.centralizer (L : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hVc hv) l hl).symm
  · exact h'

theorem Coordinates.le_of_le_normalizer {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) : V ≤ L := by
  rw [← c.commutator_eq]
  refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
  rw [commutatorElement_def]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVL hv) l).mp hl) (L.inv_mem hl)

theorem Coordinates.blockU_eq {L V : Subgroup G} {hV : IsElemAbelian 2 V} (hVL : V ≤ L)
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    (hU : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ V) :
    blockU L = V := by
  have hQ := c.blockQ_eq hC
  have hVQ : V ≤ blockQ L := by
    rw [hQ]
    exact le_inf hVL (CFSG.Quasithin.B2F.le_centralizer_self hV)
  refine le_antisymm ?_ ?_
  · rw [blockU, hQ]
    exact Subgroup.commutator_le.mpr fun x hx l hl => hU x hx l hl
  · calc V = ⁅V, L⁆ := c.commutator_eq.symm
      _ ≤ ⁅blockQ L, L⁆ := Subgroup.commutator_mono hVQ le_rfl
      _ = blockU L := rfl

theorem Coordinates.blockZ_eq {L V : Subgroup G} {hV : IsElemAbelian 2 V} (hVL : V ≤ L)
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    (hU : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ V) :
    blockZ L = ⊥ := by
  have hUe := c.blockU_eq hVL hC hU
  have hZle : blockZ L ≤ V := by
    rw [blockZ, hUe]
    exact inf_le_left
  have hLCC : L ≤ Subgroup.centralizer ((Subgroup.centralizer (L : Set G)) : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx l hl).symm
  have hLCL : L ≤ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set G)) : Set G) :=
    hLCC.trans (Subgroup.centralizer_le_normalizer (Subgroup.centralizer (L : Set G) : Set G))
  have hLN : L ≤ Subgroup.normalizer (blockZ L : Set G) := by
    rw [blockZ, hUe]
    exact CFSG.Quasithin.B2F.le_normalizer_inf hLV hLCL
  rcases c.irreducible hZle hLN with h | h
  · exact h
  · exfalso
    apply c.not_central
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvZ : v ∈ blockZ L := h ▸ hv
    have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
      rw [blockZ] at hvZ
      exact hvZ.2
    exact (Subgroup.mem_centralizer_iff.mp hvC l hl).symm

theorem Coordinates.ker_α {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    c.α.ker = CFSG.pCore 2 ↥L := by
  have hQ := c.blockQ_eq hC
  have hsub : ((CFSG.pCore 2 ↥L).map L.subtype).subgroupOf L = CFSG.pCore 2 ↥L := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rwa [← Subtype.ext hxy]
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [c.α_ker, ← hQ, CFSG.AGLEmbedding.NoXBlock.blockQ_eq_map L]
  exact hsub

theorem Coordinates.isShort2 {L V : Subgroup G} {hV : IsElemAbelian 2 V} (hVL : V ≤ L)
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hn : 2 ≤ n) (hperf : ⁅L, L⁆ = L)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    (hU : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ V) :
    IsShort2 L := by
  have hQ := c.blockQ_eq hC
  have hUe := c.blockU_eq hVL hC hU
  have hZe := c.blockZ_eq hVL hC hU
  have hVQ : V ≤ blockQ L := by
    rw [hQ]
    exact le_inf hVL (CFSG.Quasithin.B2F.le_centralizer_self hV)
  have hVC : V ≤ Subgroup.centralizer ((blockQ L : Subgroup G) : Set G) := by
    rw [hQ]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hperf' : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
    Group.isPerfect_def.mp hperfL
  have hαker : c.α.ker = CFSG.pCore 2 ↥L := c.ker_α hC
  have htype : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
    left
    have h4 : 4 ≤ Nat.card c.K := by
      rw [c.cardK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) c.K :=
      (QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective c.α c.α_surj)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.Quasithin.C126.Nat.isQuasisimple_sl2 h4)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, htype, ⟨?_, ?_⟩⟩
  · intro N hN hN2
    haveI : N.Normal := hN
    by_contra hNtop
    haveI : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
    haveI : Group.IsNilpotent (↥L ⧸ N) := hN2.isNilpotent
    haveI : Group.IsSolvable (↥L ⧸ N) := inferInstance
    have hle : (⊤ : Subgroup ↥L) ≤ N :=
      Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := N) (H := ⊤) hperf'
    exact hNtop (top_le_iff.mp hle)
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp hx.2) v (hVQ hv)
    have hxQ : x ∈ blockQ L := by
      rw [hQ]
      exact ⟨hx.1, hxV⟩
    exact hxQ
  · rw [hUe]
    exact le_inf hVQ hVC
  · intro x hx
    rw [hUe] at hx
    exact hV.2 x hx
  · rw [hZe, hUe]
    exact bot_lt_iff_ne_bot.mpr c.V_ne_bot
  · intro W hZW hWU hLW
    rw [hZe] at hZW
    rw [hUe] at hWU
    rw [hZe, hUe]
    exact c.irreducible hWU hLW

theorem Coordinates.isLin2Type {L V : Subgroup G} {hV : IsElemAbelian 2 V} (hVL : V ≤ L)
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ} (c : Coordinates L V hV hLV n)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    (hU : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ V) :
    IsLin2Type L n := by
  have hUe := c.blockU_eq hVL hC hU
  have hZe := c.blockZ_eq hVL hC hU
  have hαker := c.ker_α hC
  letI : Fintype c.K := Fintype.ofFinite c.K
  have hcard : Fintype.card c.K = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact c.cardK
  let eβ : ↥(blockU L) ≃* ↥V := MulEquiv.subgroupCongr hUe
  let β : ↥(blockU L) →* Multiplicative (Fin 2 → c.K) := c.β.comp eβ.toMonoidHom
  have hβs : Function.Surjective β := by
    simpa [β] using c.β_bij.2.comp eβ.surjective
  have hβker : β.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : c.β (eβ x) = 1 := h
      have h2 : eβ x = 1 := c.β_bij.1 (by rw [h1, map_one])
      exact eβ.injective (by simpa using h2)
    · intro h
      rw [h, map_one]
  have hβeq : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (c.α ℓ : Matrix (Fin 2) (Fin 2) c.K).mulVec (Multiplicative.toAdd (β u)) := by
    intro ℓ u v huv
    have hconj : eβ v = conjV hLV ℓ (eβ u) := by
      apply Subtype.ext
      change (v : G) = (ℓ : G) * (eβ u : G) * (ℓ : G)⁻¹
      rw [huv]
      rfl
    calc Multiplicative.toAdd (β v)
        = Multiplicative.toAdd (c.β (eβ v)) := rfl
      _ = Multiplicative.toAdd (c.β (conjV hLV ℓ (eβ u))) := by rw [hconj]
      _ = Multiplicative.toAdd (Multiplicative.ofAdd (((c.α ℓ : Matrix.SpecialLinearGroup (Fin 2) c.K) :
            Matrix (Fin 2) (Fin 2) c.K).mulVec (Multiplicative.toAdd (c.β (eβ u))))) := by
          rw [c.β_act]
      _ = (c.α ℓ : Matrix (Fin 2) (Fin 2) c.K).mulVec (Multiplicative.toAdd (β u)) := rfl
  have hker : β.ker = (blockZ L).subgroupOf (blockU L) := by
    rw [hZe]
    simpa using hβker
  exact ⟨c.K, c.fieldK, inferInstance, hcard, c.α, c.α_surj, hαker, β, hβs, hker, hβeq⟩

theorem inClassXBlock_of_binaryNaturalSL {L V : Subgroup G} (hV : IsElemAbelian 2 V) (hVL : V ≤ L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSL (barSub (⊥ : Subgroup G) V hV L) ⊤ ⊥ 2 n)
    (hperf : ⁅L, L⁆ = L)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    (hU : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ V) :
    InClassXBlock L := by
  obtain ⟨c⟩ := exists_coordinates hV hLV hnat
  refine ⟨c.isShort2 hVL hn hperf hC hU, Or.inl ⟨n, by omega, c.isLin2Type hVL hC hU⟩⟩

theorem inClassX_of_binaryNaturalSL {G : Type} [Group G] [Finite G] {L V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVL : V ≤ L) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (hn : 2 ≤ n)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (barSub ⊥ V hV L) ⊤ ⊥ 2 n)
    (hperf : ⁅L, L⁆ = L)
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    (hU : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, ⁅x, l⁆ ∈ V) :
    CFSG.RankThree.PartOne.InClassX ↥L :=
  CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock
    (inClassXBlock_of_binaryNaturalSL hV hVL hLV hn hnat hperf hC hU)
