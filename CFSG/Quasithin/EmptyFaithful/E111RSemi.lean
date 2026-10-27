module

public import CFSG.Quasithin.EmptyFaithful.E111RFam
public import CFSG.Quasithin.EmptyFaithful.E111RComp
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
open scoped commutatorElement

namespace SemiFam

variable {G : Type} [Group G] {𝒟 : Set (Subgroup G)} {D : Subgroup G}

theorem subset (h : SemiFam 𝒟) {𝒟' : Set (Subgroup G)} (h' : 𝒟' ⊆ 𝒟) : SemiFam 𝒟' :=
  ⟨fun D hD => h.simple D (h' hD), fun D hD => h.nonabelian D (h' hD),
    fun D hD D' hD' hne => h.comm D (h' hD) D' (h' hD') hne⟩

theorem commutator_self (h : SemiFam 𝒟) (hD : D ∈ 𝒟) : ⁅D, D⁆ = D := by
  have := (h.subset (Set.singleton_subset_iff.mpr hD)).commutator_eq
  rwa [sSup_singleton] at this

end SemiFam

variable {Q : Type} [Group Q] [Finite Q] {𝒟 : Set (Subgroup Q)}

omit [Finite Q] in
theorem centralizer_normal {E : Subgroup Q} (hEn : E.Normal) :
    (Subgroup.centralizer (E : Set Q)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro e he
  have h1 := hx (g⁻¹ * e * g) (by simpa using hEn.conj_mem e he g⁻¹)
  calc e * (g * x * g⁻¹) = g * ((g⁻¹ * e * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * e := by group

theorem inf_centralizer_eq_bot (h𝒟 : SemiFam 𝒟) :
    sSup 𝒟 ⊓ Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q) = ⊥ := by
  refine h𝒟.eq_bot_of_isSolvable inf_le_left (fun e he => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcx : ∀ y ∈ sSup 𝒟 ⊓ Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q),
        e * y * e⁻¹ = y :=
      fun y hy => by
        rw [Subgroup.mem_centralizer_iff.mp hy.2 e he, mul_inv_cancel_right]
    constructor
    · intro hx
      rw [hcx x hx]
      exact hx
    · intro hx
      have := hcx _ hx
      have h2 : x = e * x * e⁻¹ := by
        calc x = e⁻¹ * (e * x * e⁻¹) * e := by group
          _ = e⁻¹ * (e * (e * x * e⁻¹) * e⁻¹) * e := by rw [this]
          _ = e * x * e⁻¹ := by group
      rw [h2]
      exact hx
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    exact (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2.1).symm

theorem ne_bot_of_isComponent' {X : Type*} [Group X] {L : Subgroup X} (hL : CFSG.IsComponent L) :
    L ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  apply hab
  have : Subsingleton (L ⧸ Subgroup.center L) := by
    have : Subsingleton L := by
      rw [h]
      infer_instance
    infer_instance
  exact Subsingleton.elim _ _

omit [Finite Q] in
theorem conjSub_map {Q' : Type*} [Group Q'] (f : Q →* Q') (q : Q) (H : Subgroup Q) :
    A1b.conjSub (f q) (H.map f) = (A1b.conjSub q H).map f := by
  unfold A1b.conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h
  simp [MulAut.conj_apply]

omit [Finite Q] in
theorem pow_mem_of_sup {E B₀ : Subgroup Q} (hEn : E.Normal) (hEB : E ⊔ B₀ = ⊤)
    (hB₀ : IsPGroup 2 B₀) (x : Q) : ∃ k : ℕ, x ^ 2 ^ k ∈ E := by
  have hx : x ∈ E ⊔ B₀ := hEB ▸ Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, hk⟩ := hB₀ ⟨z, hz⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
    show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, QuotientGroup.mk_one]

section Residuals

variable (h𝒟 : SemiFam 𝒟) (hEn : (sSup 𝒟).Normal)
include h𝒟 hEn

theorem twoResidual_eq (h2 : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ sSup 𝒟) :
    twoResidual (⊤ : Subgroup Q) = sSup 𝒟 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_top
    (Subgroup.normalizer_eq_top_iff.mpr hEn).ge fun y _ => h2 y) fun x hx => ?_
  rw [mem_twoResidual_iff]
  intro N _ hN h2N
  have hNn : N.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_top g))
    n).mp hn⟩
  refine (sSup_le fun D hD => ?_ : sSup 𝒟 ≤ N) hx
  have := h𝒟.simple D hD
  have hnD : ((N ⊓ D).subgroupOf D).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    infer_instance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ D).subgroupOf D) with h1 | h1
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at h1
    have h2D : IsPGroup 2 ↥D := by
      intro d
      obtain ⟨k, hk⟩ := h2N d (Subgroup.mem_top _)
      refine ⟨k, Subtype.ext ?_⟩
      have hmem : (d : Q) ^ 2 ^ k ∈ N ⊓ D := ⟨hk, D.pow_mem d.2 _⟩
      simpa using (Subgroup.disjoint_def.mp h1) hmem hmem.2
    have := h2D.isNilpotent
    exact not_nonabelian_of_isSolvable inferInstance (h𝒟.nonabelian D hD)
  · rw [Subgroup.subgroupOf_eq_top] at h1
    exact h1.trans inf_le_left

theorem perfectCore_eq {B₀ : Subgroup Q} (hEB : sSup 𝒟 ⊔ B₀ = ⊤) (hB₀ : IsPGroup 2 B₀) :
    perfectCore (⊤ : Subgroup Q) = sSup 𝒟 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_perfectCore_of_perfect le_top h𝒟.commutator_eq)
  have := hB₀.isNilpotent
  exact perfectCore_le_of_sup_solvable le_top inferInstance hEB.symm inferInstance

end Residuals

omit [Finite Q] in
@[expose] def conjAut {B D : Subgroup Q} (hBN : B ≤ Subgroup.normalizer (D : Set Q)) :
    ↥B →* MulAut ↥D where
  toFun b :=
    { toFun := fun d => ⟨b * d * (b : Q)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBN b.2) d).mp d.2⟩
      invFun := fun d => ⟨(b : Q)⁻¹ * d * b, by
        have := (Subgroup.mem_normalizer_iff.mp (hBN (B.inv_mem b.2)) d).mp d.2
        simpa using this⟩
      left_inv := fun d => Subtype.ext (by simp [mul_assoc])
      right_inv := fun d => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun d => Subtype.ext (by simp)
  map_mul' := fun x y => MulEquiv.ext fun d => Subtype.ext (by simp [mul_assoc])

theorem card_barRad_le {n : ℕ} {B D₀ : Subgroup Q} (hBN : B ≤ Subgroup.normalizer (D₀ : Set Q))
    (hB : IsElemAbelian 2 B)
    (hBC : B ⊓ Subgroup.centralizer (D₀ : Set Q) ≤ CFSG.solvableRadical Q)
    (hrank : ∀ B' : Subgroup (MulAut ↥D₀), IsElemAbelian 2 B' → Nat.card ↥B' ≤ 2 ^ n) :
    Nat.card ↥(E1.barRad Q B) ≤ 2 ^ n := by
  set φ := conjAut hBN with hφ
  set ψ := (QuotientGroup.mk' (CFSG.solvableRadical Q)).comp B.subtype with hψ
  have hrange : E1.barRad Q B = ψ.range := by
    unfold E1.barRad
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker ≤ ψ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    have hbc : (b : Q) ∈ Subgroup.centralizer (D₀ : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg (fun f : MulAut ↥D₀ => ((f ⟨d, hd⟩ : ↥D₀) : Q)) hb
      simp only [hφ, conjAut, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
        MulAut.one_apply] at h1
      calc d * b = b * d * (b : Q)⁻¹ * b := by rw [h1]
        _ = b * d := by group
    rw [hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hBC ⟨b.2, hbc⟩
  have h1 : Nat.card ψ.range ≤ Nat.card φ.range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have h2 : IsElemAbelian 2 φ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← ha, ← hb, ← map_mul]
      rw [hB.1.is_comm.comm a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (hB.2 a a.2), map_one]
  rw [hrange]
  exact h1.trans (hrank _ h2)

section Quotient

variable (h𝒟 : SemiFam 𝒟) (hEn : (sSup 𝒟).Normal)
  (hC : IsPGroup 2 (Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q)))
include h𝒟 hEn hC

theorem solvableRadical_eq :
    CFSG.solvableRadical Q = Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := sSup 𝒟
  set R := CFSG.solvableRadical Q
  have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  have hRE : R ⊓ E = ⊥ := by
    rw [inf_comm]
    refine h𝒟.eq_bot_of_isSolvable inf_le_left (fun e he => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer he, (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
          (Subgroup.mem_top e)⟩
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
  have hc : ⁅R, E⁆ = ⊥ := le_bot_iff.mp (hRE ▸ Subgroup.commutator_le_inf R E)
  refine le_antisymm (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) ?_
  have hCn := centralizer_normal hEn
  have := hC.isNilpotent
  exact le_sSup ⟨hCn, inferInstance⟩

theorem centralizer_map_eq_bot :
    Subgroup.centralizer (((sSup 𝒟).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) :
      Subgroup (Q ⧸ CFSG.solvableRadical Q)) : Set (Q ⧸ CFSG.solvableRadical Q)) = ⊥ := by
  have hR := solvableRadical_eq h𝒟 hEn hC
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hR,
    Subgroup.mem_centralizer_iff]
  intro e he
  have h1 := Subgroup.mem_centralizer_iff.mp hy (QuotientGroup.mk' _ e) ⟨e, he, rfl⟩
  simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  rw [hR] at h1
  have hE : (e * x)⁻¹ * (x * e) ∈ sSup 𝒟 := by
    have h3 : (e * x)⁻¹ * (x * e) = (x⁻¹ * e⁻¹ * x) * e := by group
    rw [h3]
    refine (sSup 𝒟).mul_mem ?_ he
    simpa using hEn.conj_mem _ ((sSup 𝒟).inv_mem he) x⁻¹
  have h4 : (e * x)⁻¹ * (x * e) ∈ sSup 𝒟 ⊓ Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q) :=
    ⟨hE, h1⟩
  rw [inf_centralizer_eq_bot h𝒟, Subgroup.mem_bot] at h4
  have h5 : x * e = e * x := by
    have := congrArg (fun z => e * x * z) h4
    simpa [mul_assoc] using this
  exact h5.symm

theorem isComponent_map {D : Subgroup Q} (hD : D ∈ 𝒟) :
    CFSG.IsComponent (D.map (QuotientGroup.mk' (CFSG.solvableRadical Q))) := by
  have hR := solvableRadical_eq h𝒟 hEn hC
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q) with hπ
  have hDE : D ≤ sSup 𝒟 := le_sSup hD
  have hinj : Function.Injective (π.subgroupMap D) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have h1 : (d : Q) ∈ CFSG.solvableRadical Q := by
      have h0 : π (d : Q) = 1 := congrArg Subtype.val hd
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    rw [hR] at h1
    have h2 : (d : Q) ∈ sSup 𝒟 ⊓ Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q) :=
      ⟨hDE d.2, h1⟩
    rw [inf_centralizer_eq_bot h𝒟, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  set e : ↥D ≃* ↥(D.map π) :=
    MulEquiv.ofBijective (π.subgroupMap D) ⟨hinj, π.subgroupMap_surjective D⟩
  have := h𝒟.simple D hD
  have hs : IsSimpleGroup ↥(D.map π) := (MulEquiv.isSimpleGroup_congr e).mp this
  obtain ⟨a, b, hab⟩ := h𝒟.nonabelian D hD
  have hnab : ∃ a b : ↥(D.map π), a * b ≠ b * a :=
    ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  refine ⟨Vol2.Ch11.SecE3.isQuasisimple_of_simple hnab, ?_⟩
  have hEn' : ((sSup 𝒟).map π).Normal := hEn.map π (QuotientGroup.mk'_surjective _)
  have hDE' : D.map π ≤ (sSup 𝒟).map π := Subgroup.map_mono hDE
  have hDn : ((D.map π).subgroupOf ((sSup 𝒟).map π)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDE']
    exact (Subgroup.map_mono (h𝒟.le_normalizer hD)).trans (Subgroup.le_normalizer_map π)
  exact Subgroup.IsSubnormal.trans hDE' hDn.isSubnormal hEn'.isSubnormal

theorem layer_quot_eq : CFSG.layer (Q ⧸ CFSG.solvableRadical Q) =
    (sSup 𝒟).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) := by
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q)
  have hEn' : ((sSup 𝒟).map π).Normal := hEn.map π (QuotientGroup.mk'_surjective _)
  refine le_antisymm (sSup_le fun L hL => ?_) ?_
  · rcases CFSG.LocalCores.component_normal_subgroup hL hEn' with h | h
    · exact h
    · exfalso
      have hLC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      rw [centralizer_map_eq_bot h𝒟 hEn hC] at hLC
      exact ne_bot_of_isComponent' hL (le_bot_iff.mp hLC)
  · rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun D => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hD => le_sSup (isComponent_map h𝒟 hEn hC hD)

theorem mem_normalizer_of_map {D : Subgroup Q} (hD : D ∈ 𝒟) {b : Q}
    (hb : QuotientGroup.mk' (CFSG.solvableRadical Q) b ∈ Subgroup.normalizer
      ((D.map (QuotientGroup.mk' (CFSG.solvableRadical Q)) :
        Subgroup (Q ⧸ CFSG.solvableRadical Q)) : Set (Q ⧸ CFSG.solvableRadical Q))) :
    b ∈ Subgroup.normalizer (D : Set Q) := by
  have hR := solvableRadical_eq h𝒟 hEn hC
  set R := CFSG.solvableRadical Q with hRdef
  set π := QuotientGroup.mk' R with hπ
  have hle : A1b.conjSub b D ≤ D ⊔ R := by
    intro y hy
    rw [A1b.mem_conjSub_iff] at hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hb (π (b⁻¹ * y * b))).mp ⟨_, hy, rfl⟩
    have h2 : π y ∈ D.map π := by
      have e1 : π b * π (b⁻¹ * y * b) * (π b)⁻¹ = π y := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rwa [e1] at h1
    have h3 : y ∈ (D.map π).comap π := h2
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
  have hperf : ⁅A1b.conjSub b D, A1b.conjSub b D⁆ = A1b.conjSub b D := by
    unfold A1b.conjSub
    rw [← Subgroup.map_commutator, h𝒟.commutator_self hD]
  have hcore : perfectCore (D ⊔ R) ≤ D := by
    have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
    refine perfectCore_le_of_sup_solvable le_sup_left ?_ rfl hRs
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun r hr => ?_
    rw [hR] at hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ D
    · have hc := Subgroup.mem_centralizer_iff.mp hr x (le_sSup hD hx)
      rw [← hc, mul_inv_cancel_right]
    · constructor
      · intro h
        exact absurd h hx
      · intro h
        have hc := Subgroup.mem_centralizer_iff.mp hr _ (le_sSup hD h)
        have : x = r * x * r⁻¹ := by
          calc x = r⁻¹ * (r * x * r⁻¹ * r) := by group
            _ = r⁻¹ * (r * (r * x * r⁻¹)) := by rw [hc]
            _ = r * x * r⁻¹ := by group
        exact absurd (this ▸ h) hx
  have h3 : A1b.conjSub b D ≤ D := (le_perfectCore_of_perfect hle hperf).trans hcore
  have hcard : Nat.card ↥(A1b.conjSub b D) = Nat.card ↥D := by
    unfold A1b.conjSub
    exact Subgroup.card_map_of_injective (MulAut.conj b).injective
  exact mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge h3 hcard.ge)

theorem eTwo_of_semiFam {B₀ S B : Subgroup Q} (hEB : sSup 𝒟 ⊔ B₀ = ⊤) (hB₀ : IsPGroup 2 B₀)
    {D₀ : Subgroup Q} (hD₀ : D₀ ∈ 𝒟) {Γ : Subgroup Q} (hΓ : Γ ≤ E1.tauOf ⊤ S B)
    (htr : ⨆ (t : Q) (_ : t ∈ Γ), A1b.conjSub t D₀ = sSup 𝒟)
    (hcase : D₀ = ⁅D₀, B⁆ ∨
      (¬ B ≤ Subgroup.normalizer (D₀ : Set Q) ∧ Nat.card ↥(E1.barRad Q B) = 2)) :
    E1.ETwo Q S B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := solvableRadical_eq h𝒟 hEn hC
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q) with hπ
  have h2 := pow_mem_of_sup hEn hEB hB₀
  have hlayer := layer_quot_eq h𝒟 hEn hC
  have hconjE : ∀ q : Q, A1b.conjSub q D₀ ≤ sSup 𝒟 := fun q y hy => by
    rw [A1b.mem_conjSub_iff] at hy
    have h3 := hEn.conj_mem _ (le_sSup hD₀ hy) q
    have e3 : q * (q⁻¹ * y * q) * q⁻¹ = y := by group
    rwa [e3] at h3
  refine ⟨?_, ?_, ?_, D₀.map π, isComponent_map h𝒟 hEn hC hD₀, ?_, ?_⟩
  · rw [hR]
    refine ⟨_, ⟨le_rfl, hC, by rw [Subgroup.relIndex_self]; norm_num⟩, ?_⟩
    rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [E1.pCore_two_quotient_eq_top_iff]
    intro x
    obtain ⟨k, hk⟩ := h2 x
    refine ⟨k, Subgroup.mem_comap.mpr ?_⟩
    rw [hlayer]
    exact Subgroup.mem_map_of_mem π hk
  · rw [twoResidual_eq h𝒟 hEn h2, perfectCore_eq h𝒟 hEn hEB hB₀]
  · rw [hlayer]
    refine le_antisymm ?_ (iSup₂_le fun t ht => ?_)
    · rw [← htr, Subgroup.map_iSup]
      refine iSup_le fun t => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun ht => ?_
      refine le_iSup₂_of_le (π t) (Subgroup.mem_map_of_mem π (hΓ ht)) ?_
      rw [conjSub_map]
    · obtain ⟨q, -, rfl⟩ := ht
      rw [conjSub_map]
      exact Subgroup.map_mono (hconjE q)
  · rcases hcase with h | ⟨h1, h2'⟩
    · left
      unfold E1.barRad
      rw [← Subgroup.map_commutator, ← h]
    · right
      refine ⟨fun hle => h1 fun b hb => ?_, h2'⟩
      exact mem_normalizer_of_map h𝒟 hEn hC hD₀ (hle ⟨b, hb, rfl⟩)

end Quotient

end CFSG.Quasithin.E2.E22N.E111R
