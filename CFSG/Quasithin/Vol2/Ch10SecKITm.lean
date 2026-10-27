module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieCoprime
public import CFSG.Quasithin.Vol2.Ch10SecKITd
public import CFSG.Quasithin.Vol2.Ch10SecKITf

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF

variable {G : Type} [Group G] [Finite G] {M T L X : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem modO2Image_mono {A B : Subgroup G} (hAB : A ≤ B) : modO2Image L A ≤ modO2Image L B := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hx)), rfl⟩

theorem le_centralizer_pCoreOf (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) (h : IsNatBlock X n) (hA : X ⊓ pCoreOf 2 L = ⊥)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L with hQdef
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hXC : X ≤ Subgroup.centralizer (Q : Set G) := by
    have hc := commutator_le_inf hT hL hX hXL
    rw [hA, le_bot_iff, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
    exact hc
  set C := L ⊓ Subgroup.centralizer (Q : Set G) with hC
  have hCL : C ≤ L := inf_le_left
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      Vol2Native.L239.Lie.normalizer_le_normalizer_centralizer Q (hLQ hg)⟩
  have hCbn : (modO2Image L C).Normal := by
    constructor
    intro y hy g
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ g
    refine ⟨l * c * l⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hLC l.2) c).mp (Subgroup.mem_subgroupOf.mp hc)
  have hq' : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      (modO2Image L C) with hle | htop
  · exfalso
    have hXb : modO2Image L X ≤ Subgroup.center _ :=
      (modO2Image_mono (le_inf hXL hXC)).trans hle
    obtain ⟨e⟩ := xbar_equiv_of_inf_eq_bot hXL hA
    have hab : X ≤ Subgroup.centralizer (X : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_center_iff.mp (hXb (e ⟨y, hy⟩).2) (e ⟨x, hx⟩)
      have h2 : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by
        rw [map_mul, map_mul]
        exact Subtype.ext h1
      have h3 := congrArg Subtype.val (e.injective h2)
      simpa using h3.symm
    have h0 := h.inf_centralizer_self
    rw [inf_eq_left.mpr hab] at h0
    have hU : blockU X = ⊥ := le_bot_iff.mp (h0 ▸ h.blockU_le)
    have := h.1.2.2.2.2.1
    rw [hU, h.2.2.1] at this
    exact lt_irrefl _ this
  · have hLCQ : L ≤ C ⊔ Q := le_sup_of_xbar_le le_rfl (le_top.trans htop.ge)
    have hsup : L = C ⊔ (L ⊓ Q) := by
      rw [inf_eq_right.mpr hQL]
      exact le_antisymm hLCQ (sup_le hCL hQL)
    have hs : Group.IsSolvable ↥(L ⊓ Q) := by
      have := ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le
        (inf_le_right : L ⊓ Q ≤ Q)).isNilpotent
      infer_instance
    have hcore := perfectCore_le_of_sup_solvable hCL
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mpr hLC) hsup hs
    rw [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hL)] at hcore
    exact hcore.trans inf_le_right

theorem pCore_eq_bot (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) (h : IsNatBlock X n) (hA : X ⊓ pCoreOf 2 L = ⊥)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hodd : ¬ 2 ∣ (modO2Image L X).index) :
    CFSG.pCore 2 ↥L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC := le_centralizer_pCoreOf hT hL hX hXL h hA hq
  set N := CFSG.pCore 2 ↥L with hNdef
  have : N.Normal := CFSG.pCore_normal
  have hNc : ∀ x ∈ N, ∀ l : ↥L, x * l = l * x := by
    intro x hx l
    have hxQ : (x : G) ∈ pCoreOf 2 L := (C1Pack.coe_mem_pCoreOf_iff L x).mpr hx
    have := Subgroup.mem_centralizer_iff.mp (hLC l.2) _ hxQ
    exact Subtype.ext this
  have : IsMulCommutative ↥N :=
    ⟨⟨fun a b => Subtype.ext (hNc a a.2 b)⟩⟩
  set K : Subgroup ↥L := X.subgroupOf L with hK
  have hNK : N ⊓ K = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : (x : G) ∈ X ⊓ pCoreOf 2 L :=
      ⟨Subgroup.mem_subgroupOf.mp hx.2, (C1Pack.coe_mem_pCoreOf_iff L x).mpr hx.1⟩
    rw [hA, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hcomap : N ⊔ K = (modO2Image L X).comap (QuotientGroup.mk' N) := by
    ext l
    rw [Subgroup.mem_comap]
    constructor
    · intro hl
      rw [sup_comm] at hl
      obtain ⟨b, hb, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hl
      refine ⟨b, hb, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      simpa using ha
    · rintro ⟨b, hb, hbl⟩
      have h1 : b⁻¹ * l ∈ N := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hbl
        exact hbl
      have e : l = (b * (b⁻¹ * l) * b⁻¹) * b := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((inferInstance : N.Normal).conj_mem _ h1 b))
        (Subgroup.mem_sup_right hb)
  have hidx : (N ⊔ K).index = (modO2Image L X).index := by
    rw [hcomap]
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hcop : Nat.Coprime (N ⊔ K).index (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk, hidx]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  obtain ⟨D, -, hND, hNDt⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N (N ⊔ K) K hcop hNK rfl
  have hdec : ∀ l : ↥L, ∃ c ∈ N, ∃ d ∈ D, l = c * d := by
    intro l
    have hl : l ∈ D ⊔ N := by rw [sup_comm, hNDt]; exact Subgroup.mem_top l
    obtain ⟨d, hd, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hl
    exact ⟨c, hc, d, hd, (hNc c hc d).symm⟩
  have hDn : D.Normal := by
    constructor
    intro x hx l
    obtain ⟨c, hc, d, hd, rfl⟩ := hdec l
    have e : c * d * x * (c * d)⁻¹ = d * x * d⁻¹ := by
      calc c * d * x * (c * d)⁻¹ = c * (d * x * d⁻¹) * c⁻¹ := by group
        _ = d * x * d⁻¹ * c * c⁻¹ := by rw [hNc c hc (d * x * d⁻¹)]
        _ = d * x * d⁻¹ := by group
    rw [e]
    exact D.mul_mem (D.mul_mem hd hx) (D.inv_mem hd)
  have hcomm : _root_.commutator ↥L ≤ D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    obtain ⟨c₁, hc₁, d₁, hd₁, rfl⟩ := hdec a
    obtain ⟨c₂, hc₂, d₂, hd₂, rfl⟩ := hdec b
    have hd : ∀ c d : ↥L, d ∈ D → (QuotientGroup.mk (c * d) : ↥L ⧸ D) = QuotientGroup.mk c :=
      fun c d hd => by rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d).mpr hd, mul_one]
    rw [hd _ _ hd₁, hd _ _ hd₂, ← QuotientGroup.mk_mul, hNc c₁ hc₁ c₂, QuotientGroup.mk_mul]
    group
  have hperf : _root_.commutator ↥L = ⊤ := by
    have hmap : (_root_.commutator ↥L).map L.subtype = L := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, perfect_of_mem_cComp hL]
    apply Subgroup.map_injective L.subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDt : D = ⊤ := eq_top_iff.mpr (hperf ▸ hcomm)
  rw [hDt, inf_top_eq] at hND
  exact hND

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
