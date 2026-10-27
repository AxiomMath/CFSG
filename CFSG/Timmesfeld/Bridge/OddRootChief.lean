module

public import CFSG.Timmesfeld.Bridge.RootClosureL2Chief

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.Timmesfeld.Bridge.RootClosure CFSG.Open
open scoped commutatorElement

variable {K : Type} [Group K]

structure OddRootChief (D : Set K) (V : Subgroup K) [V.Normal] (x a b : K) (n : ℕ) : Prop where
  oddT : IsOddTransp D
  normal : IsNormalSet D
  x_mem : x ∈ D
  a_mem : a ∈ D
  b_mem : b ∈ D
  ab_mem : a * b ∈ D
  comm : Commute a b
  conj_b : IsConj a b
  conj_ab : IsConj a (a * b)
  conj_x : IsConj a x
  gen : Subgroup.closure {x, a, b} = ⊤
  two : IsPGroup 2 V
  ne_bot : V ≠ ⊥
  min : ∀ W : Subgroup K, W.Normal → W ≤ V → W = ⊥ ∨ W = V
  two_le : 2 ≤ n
  iso : Nonempty (K ⧸ V ≃* PSL2Model n)

namespace OddRootChief

variable [Finite K] {D : Set K} {V : Subgroup K} [hVn : V.Normal] {x a b : K} {n : ℕ}

theorem isBender (c : OddRootChief D V x a b n) : IsBenderGroup (K ⧸ V) := by
  obtain ⟨e⟩ := c.iso
  exact .isPSL2 n c.two_le e

theorem a_not_mem (c : OddRootChief D V x a b n) : a ∉ V := by
  intro haV
  have hconjV : ∀ g, IsConj a g → g ∈ V := fun g hg => by
    obtain ⟨k, rfl⟩ := isConj_iff.1 hg
    exact hVn.conj_mem a haV k
  have htop : V = ⊤ := by
    rw [eq_top_iff, ← c.gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hconjV _ c.conj_x
    · exact haV
    · exact hconjV _ c.conj_b
  obtain ⟨u, w, huw⟩ := IsBenderGroup.exists_not_commute c.isBender
  apply huw
  obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hu : (u₀ : K ⧸ V) = 1 :=
    (QuotientGroup.eq_one_iff u₀).2 (htop ▸ Subgroup.mem_top u₀)
  rw [hu]
  exact Commute.one_left _

theorem not_mem_of_conj (c : OddRootChief D V x a b n) {g : K} (hg : IsConj a g) :
    g ∉ V := by
  intro hgV
  obtain ⟨k, rfl⟩ := isConj_iff.1 hg
  apply c.a_not_mem
  have h1 := hVn.conj_mem _ hgV k⁻¹
  convert h1 using 1
  group

theorem false_of_le_center (c : OddRootChief D V x a b n)
    (hVc : V ≤ Subgroup.center K) : False := by
  have hD := c.oddT
  obtain ⟨e⟩ := c.iso
  have hsetup : Setup K {g | IsConj a g} := by
    refine ⟨⟨a, rfl⟩, ⟨?_, ?_⟩, ?_⟩
    · intro f hf
      obtain ⟨k, rfl⟩ := isConj_iff.1 hf
      rw [orderOf_conj_eq']
      exact hD.1 a c.a_mem
    · intro f hf g hg
      have hfD : f ∈ D := by
        obtain ⟨k, rfl⟩ := isConj_iff.1 hf
        exact c.normal k a c.a_mem
      have hgD : g ∈ D := by
        obtain ⟨k, rfl⟩ := isConj_iff.1 hg
        exact c.normal k a c.a_mem
      exact hD.2 f hfD g hgD
    · rw [eq_top_iff, ← c.gen]
      refine Subgroup.closure_mono ?_
      rintro g (rfl | rfl | rfl)
      · exact c.conj_x
      · exact IsConj.refl _
      · exact c.conj_b
  have hinf := inf_commutator_eq_bot_of_isBenderGroup hsetup hVc c.two c.isBender
  have hperf : commutator K = ⊤ := by
    have hab : ∀ g, IsConj a g → Abelianization.of g = Abelianization.of a := fun g hg =>
      (isConj_iff_eq.1 ((Abelianization.of (G := K)).map_isConj hg)).symm
    have hb1 : Abelianization.of b = 1 := by
      have h1 := hab _ c.conj_ab
      rw [map_mul] at h1
      exact mul_eq_left.1 h1
    have ha1 : Abelianization.of a = 1 := (hab _ c.conj_b).symm.trans hb1
    have hker : ∀ g, Abelianization.of g = 1 → g ∈ commutator K := fun g hg => by
      rw [← Abelianization.ker_of]
      exact hg
    rw [eq_top_iff, ← c.gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hker _ ((hab _ c.conj_x).trans ha1)
    · exact hker _ ha1
    · exact hker _ hb1
  rw [hperf, inf_top_eq] at hinf
  exact c.ne_bot hinf

theorem sylow_eq_sup (c : OddRootChief D V x a b n) (S : Sylow 2 K) (haS : a ∈ S) :
    (S : Subgroup K) = Subgroup.closure (D ∩ (S : Set K)) ⊔ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' V with hπ
  set P : Sylow 2 (K ⧸ V) :=
    Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective V) S with hPdef
  have hPcoe : (P : Subgroup (K ⧸ V)) = (S : Subgroup K).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective V) S
  have hL2 : CFSG.CGT.Timmesfeld75.IsL2Pair (K ⧸ V) (P : Subgroup (K ⧸ V)) (2 ^ n) :=
    CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow (f := n)
      (by have := c.two_le; omega) c.iso P
  have hVleS : V ≤ (S : Subgroup K) := c.two.le_sylow_of_normal S
  have h2P : ∀ q ∈ (P : Subgroup (K ⧸ V)), q * q = 1 := by
    intro q hq
    have h := hL2.isElemAbelian.2 q hq
    simpa [pow_two] using h
  apply le_antisymm
  · intro s hs
    by_cases h1 : π s = 1
    · have hsV : s ∈ V := (QuotientGroup.eq_one_iff s).1 h1
      simpa using Subgroup.mul_mem_sup (Subgroup.one_mem _) hsV
    · have hsp : π s ∈ (P : Subgroup (K ⧸ V)) := by
        rw [hPcoe]
        exact ⟨s, hs, rfl⟩
      have haP : π a ∈ (P : Subgroup (K ⧸ V)) := by
        rw [hPcoe]
        exact ⟨a, haS, rfl⟩
      have ha1 : π a ≠ 1 := fun h => c.a_not_mem ((QuotientGroup.eq_one_iff a).1 h)
      obtain ⟨k, hk⟩ := isConj_iff.1 (hL2.isConj_of_mul_self_eq_one (h2P _ haP) ha1
        (h2P _ hsp) h1)
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
      have hgk : π (g * a * g⁻¹) = π s := by
        rw [map_mul, map_mul, map_inv]
        exact hk
      have heD : g * a * g⁻¹ ∈ D := c.normal g a c.a_mem
      have hv : s * (g * a * g⁻¹)⁻¹ ∈ V := by
        apply (QuotientGroup.eq_one_iff _).1
        change π s * (π (g * a * g⁻¹))⁻¹ = 1
        rw [hgk, mul_inv_cancel]
      have hes : g * a * g⁻¹ ∈ (S : Subgroup K) := by
        have hvS : s * (g * a * g⁻¹)⁻¹ ∈ (S : Subgroup K) := hVleS hv
        have h2 : (s * (g * a * g⁻¹)⁻¹)⁻¹ * s = g * a * g⁻¹ := by group
        rw [← h2]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hvS) hs
      have hmemE : g * a * g⁻¹ ∈ D ∩ (S : Set K) := ⟨heD, hes⟩
      have hs_eq : s = (s * (g * a * g⁻¹)⁻¹) * (g * a * g⁻¹) := by group
      rw [hs_eq, sup_comm]
      exact Subgroup.mul_mem_sup hv (Subgroup.subset_closure hmemE)
  · refine sup_le ?_ hVleS
    rw [Subgroup.closure_le]
    intro d hd
    exact hd.2

theorem isElemAbelian_closure (c : OddRootChief D V x a b n) (S : Sylow 2 K) :
    IsElemAbelian 2 (Subgroup.closure (D ∩ (S : Set K))) := by
  have hpair : ∀ f ∈ D ∩ (S : Set K), ∀ g ∈ D ∩ (S : Set K), Commute f g :=
    fun f hf g hg => c.oddT.commute_of_isPGroup S.isPGroup' hf.1 hg.1 hf.2 hg.2
  have hPw : (D ∩ (S : Set K)).Pairwise Commute := fun f hf g hg _ => hpair f hf g hg
  refine ⟨IsMulCommutative.of_comm (fun u v => ?_), fun u hu => ?_⟩
  · exact Subtype.ext (commute_of_mem_closure hpair u.2 v.2).eq
  rw [pow_two]
  exact mul_self_eq_one_of_mem_closure hPw (fun f hf => c.oddT.mul_self_eq_one hf.1) hu

private theorem commute_commutator (c : OddRootChief D V x a b n)
    {S : Sylow 2 K} {f g : K} (hf : f ∈ D ∩ (S : Set K)) (hg : g ∈ D ∩ (S : Set K))
    {v : K} (hv : v ∈ V) : Commute g ⁅f, v⁆ := by
  have hD := c.oddT
  have hfD : f ∈ D := hf.1
  have hgD : g ∈ D := hg.1
  have hfg : Commute f g := hD.commute_of_isPGroup S.isPGroup' hfD hgD hf.2 hg.2
  have hfg2 : f * g * (f * g) = 1 := by
    rw [show f * g * (f * g) = f * (g * f) * g by group, ← hfg.eq,
      show f * (f * g) * g = f * f * (g * g) by group,
      hD.mul_self_eq_one hfD, hD.mul_self_eq_one hgD, one_mul]
  set u := v * f * v⁻¹ * f⁻¹ with hu
  have huV : u ∈ V := by
    rw [hu, show v * f * v⁻¹ * f⁻¹ = v * (f * v⁻¹ * f⁻¹) by group]
    exact V.mul_mem hv (hVn.conj_mem _ (V.inv_mem hv) f)
  have hf'D : v * f * v⁻¹ ∈ D := c.normal v f hfD
  have hsqV : v * f * v⁻¹ * g * (v * f * v⁻¹ * g) ∈ V := by
    have e1 : v * f * v⁻¹ * g * (v * f * v⁻¹ * g) =
        u * ((f * g) * u * (f * g)⁻¹) * (f * g * (f * g)) := by
      rw [hu]
      group
    rw [e1, hfg2, mul_one]
    exact V.mul_mem huV (hVn.conj_mem u huV (f * g))
  obtain ⟨k, hk⟩ := c.two ⟨_, hsqV⟩
  have hpow : (v * f * v⁻¹ * g) ^ 2 ^ (k + 1) = 1 := by
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
    rw [pow_succ', pow_mul, sq]
    exact h1
  have hcomm : Commute (v * f * v⁻¹) g := by
    rcases hD.2 _ hf'D g hgD with h2 | ho
    · exact (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hf'D)
        (hD.mul_self_eq_one hgD)).2 (orderOf_dvd_iff_pow_eq_one.1 h2)
    · have h1 : orderOf (v * f * v⁻¹ * g) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho))
          (orderOf_dvd_of_pow_eq_one hpow)
      rw [orderOf_eq_one_iff] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (Commute.refl g).inv_left
  have h' : ⁅f, v⁆ = f * (v * f * v⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h']
  exact hfg.symm.mul_right hcomm.symm.inv_right

private theorem commute_commutator_closure (c : OddRootChief D V x a b n)
    {S : Sylow 2 K} {s g : K} (hs : s ∈ Subgroup.closure (D ∩ (S : Set K)))
    (hg : g ∈ D ∩ (S : Set K)) {v : K} (hv : v ∈ V) : Commute g ⁅s, v⁆ := by
  have hEcomm : ∀ f ∈ D ∩ (S : Set K), ∀ g ∈ D ∩ (S : Set K), Commute f g :=
    fun f hf g hg => c.oddT.commute_of_isPGroup S.isPGroup' hf.1 hg.1 hf.2 hg.2
  have hgE : ∀ t ∈ Subgroup.closure (D ∩ (S : Set K)), Commute g t := fun t ht =>
    commute_of_mem_closure hEcomm (Subgroup.subset_closure hg) ht
  induction hs using Subgroup.closure_induction with
  | mem f hf => exact c.commute_commutator hf hg hv
  | one => simp
  | mul s₁ s₂ hs₁ _ ih₁ ih₂ =>
    rw [show ⁅s₁ * s₂, v⁆ = s₁ * ⁅s₂, v⁆ * s₁⁻¹ * ⁅s₁, v⁆ by
      simp only [commutatorElement_def]; group]
    exact (((hgE s₁ hs₁).mul_right ih₂).mul_right (hgE s₁ hs₁).inv_right).mul_right ih₁
  | inv s hs' ih =>
    rw [show ⁅s⁻¹, v⁆ = s⁻¹ * ⁅s, v⁆⁻¹ * s by
      simp only [commutatorElement_def]; group]
    exact (((hgE s hs').inv_right).mul_right ih.inv_right).mul_right (hgE s hs')

theorem quadratic (c : OddRootChief D V x a b n)
    {S : Sylow 2 K} (hS : (S : Subgroup K) = Subgroup.closure (D ∩ (S : Set K)) ⊔ V) :
    ∀ s ∈ (S : Subgroup K), ∀ s' ∈ (S : Subgroup K), ∀ v ∈ V, Commute s' ⁅s, v⁆ := by
  have hVcomm := commute_of_minimal c.two c.ne_bot c.min
  have hVn' : ∀ s : K, ∀ v ∈ V, ⁅s, v⁆ ∈ V := fun s v hv =>
    Subgroup.commutator_le_right (H₁ := (⊤ : Subgroup K)) (H₂ := V)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top s) hv)
  intro s hs s' hs' v hv
  rw [hS] at hs hs'
  obtain ⟨s₀, hs₀, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hs
  have e1 : ⁅s₀ * w, v⁆ = ⁅s₀, v⁆ := by
    have hwv : Commute w v := hVcomm w hw v hv
    simp only [commutatorElement_def]
    calc s₀ * w * v * (s₀ * w)⁻¹ * v⁻¹ = s₀ * (w * v * w⁻¹) * s₀⁻¹ * v⁻¹ := by group
      _ = s₀ * v * s₀⁻¹ * v⁻¹ := by rw [hwv.eq, mul_inv_cancel_right]
  rw [e1]
  obtain ⟨s₀', hs₀', w', hw', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hs'
  have h1 : Commute s₀' ⁅s₀, v⁆ :=
    Subgroup.closure_induction (p := fun x _ => Commute x ⁅s₀, v⁆)
      (fun g hg => c.commute_commutator_closure hs₀ hg hv)
      (by simp [commutatorElement_def])
      (fun a b _ _ ha hb => ha.mul_left hb)
      (fun a _ ha => ha.inv_left)
      hs₀'
  exact h1.mul_left (hVcomm w' hw' _ (hVn' s₀ v hv))

theorem exists_complement (c : OddRootChief D V x a b n)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = Subgroup.closure (D ∩ (S : Set K)) ⊔ V) :
    ∃ R : Subgroup K, V ⊓ R = ⊥ ∧ V ⊔ R = ⊤ := by
  have hVcomm := commute_of_minimal c.two c.ne_bot c.min
  have hEl : IsElemAbelian 2 (Subgroup.closure (D ∩ (S : Set K))) :=
    c.isElemAbelian_closure S
  obtain ⟨C, hCE, hC1, hC2⟩ :=
    SignalizerFunctorTheorem.McBride.Near.Lemma27.exists_isCompl_of_le Nat.prime_two hEl
      (inf_le_left : Subgroup.closure (D ∩ (S : Set K)) ⊓ V ≤
        Subgroup.closure (D ∩ (S : Set K))) le_rfl
  have : IsMulCommutative V :=
    IsMulCommutative.of_comm fun u w => Subtype.ext (hVcomm u u.2 w w.2).eq
  have hVC : V ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [← hC1]
    exact ⟨⟨hCE hg.2, hg.1⟩, hg.2⟩
  have hVCS : V ⊔ C = S := by
    rw [hS]
    apply le_antisymm
    · exact sup_le le_sup_right (hCE.trans le_sup_left)
    · refine sup_le ?_ le_sup_left
      rw [← hC2]
      exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  exact SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement Nat.prime_two
    c.two S (hS ▸ le_sup_right) hVC hVCS

private theorem exists_sylow_pair (c : OddRootChief D V x a b n) :
    ∃ S : Sylow 2 K, a ∈ S ∧ b ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := c.oddT
  have hpair : ({a, b} : Set K).Pairwise Commute := by
    intro u hu v hv huv
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · rcases Set.mem_insert_iff.1 hv with rfl | hv
      · exact absurd rfl huv
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        exact c.comm
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      rcases Set.mem_insert_iff.1 hv with rfl | hv
      · exact c.comm.symm
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        exact absurd rfl huv
  have h2ab : ∀ s ∈ ({a, b} : Set K), s * s = 1 := by
    intro s hs
    rcases Set.mem_insert_iff.1 hs with rfl | hs
    · exact hD.mul_self_eq_one c.a_mem
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hD.mul_self_eq_one c.b_mem
  have hP2 : IsPGroup 2 (Subgroup.closure ({a, b} : Set K)) :=
    isPGroup_closure_of_pairwise hpair h2ab
  obtain ⟨S, hSle⟩ := hP2.exists_le_sylow
  exact ⟨S, hSle (Subgroup.subset_closure (Set.mem_insert _ _)),
    hSle (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

private theorem centralizer_trivial (c : OddRootChief D V x a b n)
    (hVc : ¬ V ≤ Subgroup.center K) : ∀ v ∈ V, (∀ k : K, Commute k v) → v = 1 := by
  intro v hv hcomm
  have hZn : (V ⊓ Subgroup.center K).Normal := inferInstance
  rcases c.min _ hZn inf_le_left with h0 | h0
  · have hvZ : v ∈ V ⊓ Subgroup.center K :=
      ⟨hv, Subgroup.mem_center_iff.2 fun k => hcomm k⟩
    rw [h0, Subgroup.mem_bot] at hvZ
    exact hvZ
  · exact absurd (h0 ▸ inf_le_right) hVc

private theorem complement_upperUnipotent (c : OddRootChief D V x a b n)
    (h1 : PSL2SylowCoordStmt) (S : Sylow 2 K)
    (hS : (S : Subgroup K) = Subgroup.closure (D ∩ (S : Set K)) ⊔ V) :
    ∃ (R : Subgroup K)
      (φR : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)),
      V ⊓ R = ⊥ ∧ V ⊔ R = ⊤ ∧
        (((S : Subgroup K) ⊓ R).subgroupOf R).map φR.toMonoidHom =
          upperUnipotent (GaloisField 2 n) ∧
        ∀ k : K, ∃ v ∈ V, ∃ r ∈ R, v * r = k := by
  obtain ⟨e⟩ := c.iso
  obtain ⟨R, hVR, hVR'⟩ := c.exists_complement S hS
  set π := QuotientGroup.mk' V with hπ
  set P : Sylow 2 (K ⧸ V) :=
    Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective V) S with hPdef
  have hPcoe : (P : Subgroup (K ⧸ V)) = (S : Subgroup K).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective V) S
  obtain ⟨φ, hφ⟩ := h1 n c.two_le (K ⧸ V) ⟨e⟩ P
  have hdecomp : ∀ k : K, ∃ v ∈ V, ∃ r ∈ R, v * r = k := fun k =>
    Subgroup.mem_sup_of_normal_left.1 (hVR' ▸ Subgroup.mem_top k)
  have hπR : Function.Bijective (π.comp R.subtype) := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro r hr
      have hrV : (r : K) ∈ V := (QuotientGroup.eq_one_iff _).1 hr
      have hrVR : (r : K) ∈ V ⊓ R := ⟨hrV, r.2⟩
      rw [hVR, Subgroup.mem_bot] at hrVR
      exact Subtype.ext hrVR
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective V q
      obtain ⟨v, hv, r, hr, rfl⟩ := hdecomp k
      refine ⟨⟨r, hr⟩, ?_⟩
      show π r = π (v * r)
      rw [map_mul, show π v = 1 from (QuotientGroup.eq_one_iff v).2 hv, one_mul]
  set ψ : ↥R ≃* K ⧸ V := MulEquiv.ofBijective (π.comp R.subtype) hπR with hψ
  set φR : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := ψ.trans φ with hφR
  have hψA : (((S : Subgroup K) ⊓ R).subgroupOf R).map ψ.toMonoidHom = P := by
    ext q
    constructor
    · rintro ⟨r, hr, hq⟩
      have hrS : (r : K) ∈ (S : Subgroup K) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hr)).1
      rw [hPcoe]
      exact ⟨r, hrS, hq⟩
    · intro hq
      obtain ⟨r, hr⟩ := hπR.2 q
      refine ⟨r, Subgroup.mem_subgroupOf.2 ⟨?_, r.2⟩, hr⟩
      have hqS : q ∈ (S : Subgroup K).map π := by
        rw [hPcoe] at hq
        exact hq
      obtain ⟨s, hs, hsq⟩ := hqS
      have hrq : π (r : K) = q := hr
      have hvin : s⁻¹ * (r : K) ∈ V := by
        apply (QuotientGroup.eq_one_iff _).1
        show π s⁻¹ * π (r : K) = 1
        rw [map_inv, hsq, hrq, inv_mul_cancel]
      have heq : (r : K) = s * (s⁻¹ * (r : K)) := by group
      rw [heq]
      exact (S : Subgroup K).mul_mem hs (c.two.le_sylow_of_normal S hvin)
  have hAmap : (((S : Subgroup K) ⊓ R).subgroupOf R).map φR.toMonoidHom =
      upperUnipotent (GaloisField 2 n) := by
    rw [← hφ, ← hψA, Subgroup.map_map]
    exact congrArg (fun f => (((S : Subgroup K) ⊓ R).subgroupOf R).map f)
      (MonoidHom.ext fun _ => rfl)
  exact ⟨R, φR, hVR, hVR', hAmap, hdecomp⟩

private theorem conjClosure_range_le_normal {R : Subgroup K} {V : Subgroup K} [V.Normal]
    (hVcomm : ∀ v ∈ V, ∀ w ∈ V, Commute v w) {w : K} (hw : w ∈ V)
    (hdecomp : ∀ k : K, ∃ v ∈ V, ∃ r ∈ R, v * r = k) :
    (Subgroup.closure (Set.range fun r : ↥R => (r : K) * w * (r : K)⁻¹) ≤ V) ∧
      (Subgroup.closure (Set.range fun r : ↥R => (r : K) * w * (r : K)⁻¹)).Normal := by
  have hWV : Subgroup.closure (Set.range fun r : ↥R => (r : K) * w * (r : K)⁻¹) ≤ V := by
    rw [Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    exact (inferInstance : V.Normal).conj_mem w hw r
  refine ⟨hWV, ⟨fun g hg k => ?_⟩⟩
  obtain ⟨v', hv', r, hr, rfl⟩ := hdecomp k
  have hrg : r * g * r⁻¹ ∈ Subgroup.closure
      (Set.range fun r : ↥R => (r : K) * w * (r : K)⁻¹) := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨r', rfl⟩ := hg
      exact Subgroup.subset_closure ⟨⟨r, hr⟩ * r', by
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group⟩
    | one => simp
    | mul u u' _ _ ihu ihu' =>
      rw [show r * (u * u') * r⁻¹ = r * u * r⁻¹ * (r * u' * r⁻¹) by group]
      exact Subgroup.mul_mem _ ihu ihu'
    | inv u _ ihu =>
      rw [show r * u⁻¹ * r⁻¹ = (r * u * r⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihu
  have hcomm : Commute v' (r * g * r⁻¹) := hVcomm v' hv' _ (hWV hrg)
  rw [show v' * r * g * (v' * r)⁻¹ = v' * (r * g * r⁻¹) * v'⁻¹ by group, hcomm.eq,
    mul_inv_cancel_right]
  exact hrg

private theorem exists_natural_theta (c : OddRootChief D V x a b n)
    (hVc : ¬ V ≤ Subgroup.center K) (S : Sylow 2 K)
    (hS : (S : Subgroup K) = Subgroup.closure (D ∩ (S : Set K)) ⊔ V)
    {R : Subgroup K}
    {φR : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hAmap : (((S : Subgroup K) ⊓ R).subgroupOf R).map φR.toMonoidHom =
      upperUnipotent (GaloisField 2 n))
    (hdecomp : ∀ k : K, ∃ v ∈ V, ∃ r ∈ R, v * r = k) :
    ∃ θ : (Fin 2 → GaloisField 2 n) → K,
      ARS.IsNaturalModule φR θ ∧ Set.range θ = V := by
  have hVcomm := commute_of_minimal c.two c.ne_bot c.min
  have hfix := c.centralizer_trivial hVc
  have hVS : V ≤ (S : Subgroup K) := hS ▸ le_sup_right
  have hnil : Group.IsNilpotent ↥(S : Subgroup K) := S.isPGroup'.isNilpotent
  have hVSn : (V.subgroupOf (S : Subgroup K)).Normal := hVn.subgroupOf _
  have hne' : V.subgroupOf (S : Subgroup K) ≠ ⊥ := by
    intro h0
    apply c.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVS, h0, Subgroup.map_bot]
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥(S : Subgroup K)) hne')
  have hwV : ((y : (S : Subgroup K)) : K) ∈ V := (Subgroup.mem_inf.1 y.2).1
  have hwA : ∀ s ∈ (S : Subgroup K) ⊓ R, Commute s ((y : (S : Subgroup K)) : K) := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 y.2).2
      ⟨s, (Subgroup.mem_inf.1 hs).1⟩)
  have hw1 : ((y : (S : Subgroup K)) : K) ≠ 1 := fun h1' =>
    hy1 (Subtype.ext (Subtype.ext h1'))
  obtain ⟨θ, hθ, hθrange, -⟩ := ARS.exists_natural_of_quadratic_conj (N := V) φR hAmap
    hVcomm (fun r _ v hv => hVn.conj_mem v hv r)
    (fun v hv hcomm => hfix v hv fun k => by
      obtain ⟨v', hv', r, hr, rfl⟩ := hdecomp k
      exact (hVcomm v' hv' v hv).mul_left (hcomm r hr))
    (fun v hv s hs s' hs' => c.quadratic hS s (Subgroup.mem_inf.1 hs).1 s'
      (Subgroup.mem_inf.1 hs').1 v hv) hwV hwA hw1
  set W₁ := Subgroup.closure
    (Set.range fun r : ↥R => (r : K) * ((y : (S : Subgroup K)) : K) * (r : K)⁻¹) with hW₁
  obtain ⟨hW₁V, hW₁n⟩ := conjClosure_range_le_normal hVcomm hwV hdecomp
  have hW₁ne : W₁ ≠ ⊥ := by
    intro h0
    apply hw1
    have h' : ((y : (S : Subgroup K)) : K) ∈ W₁ := Subgroup.subset_closure ⟨1, by simp⟩
    rw [h0, Subgroup.mem_bot] at h'
    exact h'
  have hW₁eq : W₁ = V := (c.min W₁ hW₁n hW₁V).resolve_left hW₁ne
  exact ⟨θ, hθ, by rw [hθrange, hW₁eq]⟩

private theorem theta_aux {R : Subgroup K}
    {φR : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {θ : (Fin 2 → GaloisField 2 n) → K} (hθ : ARS.IsNaturalModule φR θ)
    (hθrange : Set.range θ = V)
    (hdecomp : ∀ k : K, ∃ v ∈ V, ∃ r ∈ R, v * r = k) (hVR : V ⊓ R = ⊥) :
    (∀ v, θ v ∈ V) ∧ (∀ v, θ v ∈ R → v = 0) ∧
      (∀ k : K, ∃ v, ∃ r ∈ R, k = θ v * r) := by
  have hθ0 : θ 0 = 1 := hθ.map_zero
  have hθV : ∀ v, θ v ∈ V := fun v => by
    have h' : θ v ∈ Set.range θ := ⟨v, rfl⟩
    rwa [hθrange] at h'
  refine ⟨hθV, ?_, ?_⟩
  · intro v hv
    have h' : θ v ∈ V ⊓ R := ⟨hθV v, hv⟩
    rw [hVR, Subgroup.mem_bot] at h'
    exact hθ.injective (h'.trans hθ0.symm)
  · intro k
    obtain ⟨v', hv', r, hr, rfl⟩ := hdecomp k
    have h' : v' ∈ Set.range θ := by
      rw [hθrange]
      exact hv'
    obtain ⟨v, rfl⟩ := h'
    exact ⟨v, r, hr, rfl⟩

theorem false (c : OddRootChief D V x a b n) (h1 : PSL2SylowCoordStmt)
    (h3 : NaturalComplementStmt) : False := by
  have hD := c.oddT
  by_cases hVc : V ≤ Subgroup.center K
  · exact c.false_of_le_center hVc
  obtain ⟨S, haS, hbS⟩ := c.exists_sylow_pair
  have hS := c.sylow_eq_sup S haS
  obtain ⟨R, φR, hVR, -, hAmap, hdecomp⟩ := c.complement_upperUnipotent h1 S hS
  obtain ⟨θ, hθ, hθrange⟩ := c.exists_natural_theta hVc S hS hAmap hdecomp
  obtain ⟨hθV, hθR, hθdec⟩ := theta_aux hθ hθrange hdecomp hVR
  have hFintype : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : 4 ≤ Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by have := c.two_le; omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) c.two_le
  have hθ0 : θ 0 = 1 := hθ.map_zero
  have hmem : ∀ g : K, g ∈ Subgroup.closure {x, a, b} := fun g => c.gen ▸ Subgroup.mem_top g
  have key := h3 K (GaloisField 2 n) hcard R φR θ hθ hθR hθdec x a b
    (hD.mul_self_eq_one c.x_mem) (hD.mul_self_eq_one c.a_mem) (hD.mul_self_eq_one c.b_mem)
    (fun v hv => c.not_mem_of_conj c.conj_x (hv ▸ hθV v))
    (fun v hv => c.a_not_mem (hv ▸ hθV v))
    (fun v hv => c.not_mem_of_conj c.conj_b (hv ▸ hθV v))
    (fun g => ⟨0, g, hmem g, by rw [hθ0, one_mul]⟩) ![1, 0] (hmem _)
  have h10 := congrFun key 0
  simp at h10

end OddRootChief

end CFSG.Timmesfeld.Bridge.OddRoot
