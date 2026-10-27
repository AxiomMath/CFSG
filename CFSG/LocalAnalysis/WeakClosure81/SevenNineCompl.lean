module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineLift
public import CFSG.LocalAnalysis.WeakClosure81.ThreeTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {V H E J : Subgroup G}


theorem le_barSub_commConjSup (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) :
    Zb ≤ barSub (kSub V H E) φ (commConjSup V H E) := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let K : Subgroup G := kSub V H E
  have hKH : K ≤ H := kSub_le_of_forall_le h.omega_le
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le h.pcore_le
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  refine hc.z_le.trans (iSup_le fun g => iSup_le fun _hgL => iSup_le fun h2 => ?_)
  obtain ⟨k, rfl⟩ := hφ.surjective g
  let M : Subgroup X := barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k)
  let Q : Subgroup G := barPre K φ M
  have hker_eq : φ.ker = (K ⊓ J).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hk => ⟨k.2, (hφ.ker_iff k).mp hk⟩, fun hk => (hφ.ker_iff k).mpr hk.2⟩
  have hker : IsPGroup 2 φ.ker := by
    rw [hker_eq]
    exact (hJ2.to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hQ2 : IsPGroup 2 Q := by
    dsimp only [Q, barPre]
    exact IsPGroup.map (IsPGroup.comap_of_ker_isPGroup h2 φ hker) K.subtype
  have hVQ : V ≤ Q := by
    intro w hw
    refine mem_barPre.mpr ⟨le_kSub h.mem hw, ?_⟩
    exact Subgroup.mem_sup_left (mem_barSub.mpr ⟨⟨w, le_kSub h.mem hw⟩, hw, rfl⟩)
  have hCK : conjSubgroup V (k : G) ≤ K :=
    le_kSub (conjSubgroup_mem_omegaSet h.le h.normal h.mem (hKH k.2))
  have hCQ : conjSubgroup V (k : G) ≤ Q := by
    intro w hw
    refine mem_barPre.mpr ⟨hCK hw, ?_⟩
    have hwbar : φ ⟨w, hCK hw⟩ ∈ barSub K φ (conjSubgroup V (k : G)) :=
      mem_barSub.mpr ⟨⟨w, hCK hw⟩, hw, rfl⟩
    rw [barSub_conjSubgroup (K := K) φ V k] at hwbar
    exact Subgroup.mem_sup_right hwbar
  have hP2 : IsPGroup 2 ↥(V ⊔ conjSubgroup V (k : G) ⊔ J) := by
    have hQnormJ : Q ≤ Subgroup.normalizer (J : Set G) :=
      (barPre_le K φ M).trans (hKH.trans hHJ)
    exact (hQ2.to_sup_of_normal_right' hJ2 hQnormJ).to_le
      (sup_le ((sup_le hVQ hCQ).trans le_sup_left) le_sup_right)
  rw [← barSub_conjSubgroup (K := K) φ V k]
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_barSub.mp hz
  have hcomm : ∀ u ∈ V, ∀ b ∈ conjSubgroup V (k : G), u * b = b * u :=
    seven_three_one h.elemAbelian h.ti h.abelian h.le h.normal h.mem h.omega_le
      h.pcore_le h.jnormal (hKH k.2) hP2
  have hcomm_le : conjSubgroup V (k : G) ≤ commConjSup V H E :=
    le_iSup₂_of_le (k : G) k.2 (le_iSup_of_le hcomm le_rfl)
  exact mem_barSub.mpr ⟨a, hcomm_le ha, rfl⟩

theorem exists_sevenNineCompl (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) : ∃ P : Subgroup G, SevenNineCompl (kSub V H E) J φ Yb v P := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let Y : Subgroup G := barPre K φ Yb
  let C : Subgroup G := Y ⊓ J
  have hKH : K ≤ H := kSub_le_of_forall_le h.omega_le
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le h.pcore_le
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  have hφ' : IsBarMap K (K ⊓ J) φ :=
    ⟨hφ.surjective, fun k => (hφ.ker_iff k).trans
      ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩⟩
  have hYK : Y ≤ K := barPre_le K φ Yb
  have hYH : Y ≤ H := hYK.trans hKH
  have hYnormJ : Y ≤ Subgroup.normalizer (J : Set G) := hYH.trans hHJ
  haveI hCnorm : (C.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (show C ≤ Y from inf_le_left)]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [Subgroup.mem_inf] at hc ⊢
      exact ⟨Y.mul_mem (Y.mul_mem hy hc.1) (Y.inv_mem hy),
        (Subgroup.mem_normalizer_iff.mp (hYnormJ hy) c).mp hc.2⟩
    · intro hc
      rw [Subgroup.mem_inf] at hc ⊢
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hYnormJ hy) c).mpr hc.2⟩
      rw [show c = y⁻¹ * (y * c * y⁻¹) * y by group]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hc.1) hy
  have hC2 : IsPGroup 2 C := hJ2.to_le inf_le_right
  have hCY : C.relIndex Y = Nat.card Yb := by
    have h1 : C.relIndex Y = J.relIndex Y :=
      Subgroup.inf_relIndex_left (H := Y) (K := J)
    have h2 : J.relIndex Y = (K ⊓ J).relIndex Y := by
      rw [← Subgroup.inf_relIndex_right (H := K ⊓ J) (K := Y),
        show (K ⊓ J) ⊓ Y = J ⊓ Y by rw [inf_comm K J, inf_assoc, inf_eq_right.mpr hYK]]
      exact (Subgroup.inf_relIndex_right (H := J) (K := Y)).symm
    rw [h1, h2]
    exact relIndex_barPre inf_le_left hφ' Yb
  haveI : Fact p.Prime := Fact.mk hc.prime
  have hYbP : IsPGroup p Yb := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hc.elemAbelian.2 (x : X) x.2⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hYbP
  have hodd : Odd (C.relIndex Y) := by
    rw [hCY, hn]
    exact (hc.prime.odd_of_ne_two hc.ne_two).pow
  have hcommq : ∀ a b : ↥Y ⧸ C.subgroupOf Y, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H a =>
    induction b using QuotientGroup.induction_on with | H b =>
    obtain ⟨haK, haYb⟩ := mem_barPre.mp a.2
    obtain ⟨hbK, hbYb⟩ := mem_barPre.mp b.2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Y.mul_mem (Y.inv_mem (Y.mul_mem a.2 b.2)) (Y.mul_mem b.2 a.2)
    · have hcommYb :
          φ ⟨(a : G), haK⟩ * φ ⟨(b : G), hbK⟩ =
            φ ⟨(b : G), hbK⟩ * φ ⟨(a : G), haK⟩ := by
        have h := (hc.elemAbelian.1.is_comm).comm
          (⟨φ ⟨(a : G), haK⟩, haYb⟩ : Yb) (⟨φ ⟨(b : G), hbK⟩, hbYb⟩ : Yb)
        simpa using congrArg Subtype.val h
      have hEq : (⟨(((a * b)⁻¹ * (b * a) : ↥Y) : G), hYK ((a * b)⁻¹ * (b * a)).2⟩ : ↥K) =
          (⟨(a : G), haK⟩ * ⟨(b : G), hbK⟩)⁻¹ *
            (⟨(b : G), hbK⟩ * ⟨(a : G), haK⟩) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine (hφ.ker_iff ⟨(((a * b)⁻¹ * (b * a) : ↥Y) : G),
        hYK ((a * b)⁻¹ * (b * a)).2⟩).mp ?_
      rw [hEq, map_mul, map_inv, map_mul, map_mul]
      rw [hcommYb]
      group
  haveI hCcomm : IsMulCommutative (↥Y ⧸ C.subgroupOf Y) := IsMulCommutative.of_comm hcommq
  have hnil : Group.IsNilpotent (↥Y ⧸ C.subgroupOf Y) := inferInstance
  have hv2 : v * v = 1 := elemAbelian_mul_self h.elemAbelian hvV
  have hvN : v ∈ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_barPre hφ (le_kSub h.mem) hc.s_le hvV
  have hfix : ∀ x ∈ Y, x⁻¹ * (v * x * v⁻¹) ∈ C →
      ∃ y ∈ Y, v * y = y * v ∧ x⁻¹ * y ∈ C := by
    intro x hxY hxC
    obtain ⟨hxK, hxYb⟩ := mem_barPre.mp hxY
    let x' : ↥K := ⟨x, hxK⟩
    let v' : ↥K := ⟨v, le_kSub h.mem hvV⟩
    let t : X := φ v'
    have hJx : x⁻¹ * (v * x * v⁻¹) ∈ J := (Subgroup.mem_inf.mp hxC).2
    have hker1 : φ (x'⁻¹ * (v' * x' * v'⁻¹)) = 1 := by
      apply (hφ.ker_iff _).mpr
      have hcoe : ((x'⁻¹ * (v' * x' * v'⁻¹) : ↥K) : G) = x⁻¹ * (v * x * v⁻¹) := by
        simp only [x', v', Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe]
      exact hJx
    have htcomm : Commute t (φ x') := by
      show t * φ x' = φ x' * t
      have h : (φ x')⁻¹ * (t * φ x' * t⁻¹) = 1 := by
        have hh := hker1
        simp only [map_mul, map_inv] at hh
        simpa only [t] using hh
      calc t * φ x' = φ x' * ((φ x')⁻¹ * (t * φ x' * t⁻¹)) * t := by group
        _ = φ x' * 1 * t := by rw [h]
        _ = φ x' * t := by rw [mul_one]
    have hxZ : φ x' ∈ Zb := by
      rw [hc.z_eq]
      refine ⟨hxYb, ?_⟩
      rw [SevenNineConfig.barSub_eq_zpowers h hφ hc hvV hvJ]
      exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact htcomm.zpow_left m)
    obtain ⟨r, hrC, hrφ⟩ := mem_barSub.mp (le_barSub_commConjSup h hφ hc hxZ)
    have hrY : (r : G) ∈ Y := mem_barPre.mpr ⟨r.2, by rw [hrφ]; exact hxYb⟩
    refine ⟨(r : G), hrY, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mp (commConjSup_le_centralizer V H E hrC) v hvV
    · refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.inv_mem hxY) hrY, ?_⟩
      have hker2 : φ (x'⁻¹ * r) = 1 := by
        rw [map_mul, map_inv, hrφ, inv_mul_cancel]
      have hJmem : ((x'⁻¹ * r : ↥K) : G) ∈ J := (hφ.ker_iff _).mp hker2
      have hcoe : ((x'⁻¹ * r : ↥K) : G) = x⁻¹ * (r : G) := by
        simp only [x', Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [hcoe] at hJmem
  obtain ⟨P, hPY, hPC, hPsup, hvP⟩ :=
    exists_complement_normalized_of_involution (X := Y) (Y := C) (a := v)
      (show C ≤ Y from inf_le_left) hC2 hodd hnil hv2 hvN hfix
  exact ⟨P, { le := hPY, inf_eq := hPC, sup_eq := hPsup, mem_normalizer := hvP }⟩

end CFSG.LocalAnalysis.WeakClosure81
