module

public import CFSG.Quasithin.H13.A7Nat1238NQBase
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Background.A3Structure312Nonquasi
public import CFSG.Quasithin.Background.DicksonA312
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_solvableRadical_of_mk_mem_oddCore {H K₀ : Subgroup G} (hK₀H : K₀ ≤ H) {k : G}
    (hk : k ∈ K₀)
    (hko : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hK₀H hk⟩ ∈
      (CFSG.oddCore ↥(modO2Image H K₀)).map (modO2Image H K₀).subtype) :
    k ∈ (CFSG.solvableRadical ↥K₀).map K₀.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥H with hP
  set L := modO2Image H K₀ with hL
  set OL := (CFSG.oddCore ↥L).map L.subtype with hOL
  set φ : ↥K₀ →* (↥H ⧸ P) := (QuotientGroup.mk' P).comp (Subgroup.inclusion hK₀H) with hφ
  have hφL : ∀ x : ↥K₀, φ x ∈ L := fun x =>
    ⟨Subgroup.inclusion hK₀H x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  have hOLn : ∀ l ∈ L, ∀ o ∈ OL, l * o * l⁻¹ ∈ OL := by
    rintro l hl _ ⟨o, ho, rfl⟩
    refine ⟨⟨l, hl⟩ * o * ⟨l, hl⟩⁻¹, (CFSG.oddCore_normal (G := ↥L)).conj_mem o ho _, rfl⟩
  set N := OL.comap φ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show φ (g * n * g⁻¹) ∈ OL
    rw [map_mul, map_mul, map_inv]
    exact hOLn _ (hφL g) _ hn
  have hS : Group.IsSolvable ↥OL := by
    have := A312.oddCore_isSolvable ↥L
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (CFSG.oddCore ↥L) L.subtype
        L.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (CFSG.oddCore ↥L) L.subtype L.subtype_injective).surjective
  have hker : Group.IsSolvable ↥φ.ker := by
    have h2 : IsPGroup 2 ↥φ.ker := by
      intro x
      have hx : Subgroup.inclusion hK₀H (x : ↥K₀) ∈ P := by
        have h0 : QuotientGroup.mk' P (Subgroup.inclusion hK₀H (x : ↥K₀)) = 1 := x.2
        exact (QuotientGroup.eq_one_iff _).1 h0
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
      refine ⟨m, Subtype.ext ?_⟩
      have h1 : (Subgroup.inclusion hK₀H (x : ↥K₀)) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      rw [← map_pow] at h1
      exact (Subgroup.inclusion_injective hK₀H) (by simpa using h1)
    have := h2.isNilpotent
    infer_instance
  have hNR := le_solvableRadical_of_map_le φ hS hker hNn (Subgroup.map_comap_le _ _)
  exact ⟨⟨k, hk⟩, hNR hko, rfl⟩

theorem le_sup_of_le_sup_oddCore {H K₀ Ke C : Subgroup G} (hK₀H : K₀ ≤ H) (hKeK₀ : Ke ≤ K₀)
    (hC : (CFSG.solvableRadical ↥K₀).map K₀.subtype ≤ C)
    (hL : modO2Image H K₀ ≤ modO2Image H Ke ⊔
      (CFSG.oddCore ↥(modO2Image H K₀)).map (modO2Image H K₀).subtype) :
    K₀ ≤ (K₀ ⊓ C) ⊔ Ke := by
  set P := CFSG.pCore 2 ↥H with hP
  set L := modO2Image H K₀ with hLdef
  set B := modO2Image H Ke with hB
  set OL := (CFSG.oddCore ↥L).map L.subtype with hOL
  have hBL : B ≤ L := Subgroup.map_mono fun x hx => hKeK₀ hx
  have hLN : L ≤ normalizer (OL : Set (↥H ⧸ P)) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨l, hl⟩ * o * ⟨l, hl⟩⁻¹, (CFSG.oddCore_normal (G := ↥L)).conj_mem o ho _, rfl⟩
    · intro hx
      obtain ⟨o, ho, hox⟩ := hx
      refine ⟨⟨l, hl⟩⁻¹ * o * ⟨l, hl⟩, ?_, ?_⟩
      · have := (CFSG.oddCore_normal (G := ↥L)).conj_mem o ho (⟨l, hl⟩⁻¹)
        simpa using this
      · have h1 : (o : ↥H ⧸ P) = l * x * l⁻¹ := hox
        show ((⟨l, hl⟩⁻¹ * o * ⟨l, hl⟩ : ↥L) : ↥H ⧸ P) = x
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
        group
  intro k hk
  have hkL : QuotientGroup.mk' P ⟨k, hK₀H hk⟩ ∈ L :=
    ⟨⟨k, hK₀H hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have hkBO : QuotientGroup.mk' P ⟨k, hK₀H hk⟩ ∈ OL ⊔ B := by
    rw [sup_comm]
    exact hL hkL
  obtain ⟨o, ho, b, hb, hob⟩ :=
    Setup.Family.mem_sup_of_le_normalizer (hBL.trans hLN) hkBO
  obtain ⟨x, hx, rfl⟩ := hb
  have hxKe : (x : G) ∈ Ke := Subgroup.mem_subgroupOf.1 hx
  have hxK₀ : (x : G) ∈ K₀ := hKeK₀ hxKe
  have hy : k * (x : G)⁻¹ ∈ K₀ := K₀.mul_mem hk (K₀.inv_mem hxK₀)
  have hyo : QuotientGroup.mk' P ⟨k * (x : G)⁻¹, hK₀H hy⟩ ∈ OL := by
    have h1 : (⟨k * (x : G)⁻¹, hK₀H hy⟩ : ↥H) = ⟨k, hK₀H hk⟩ * x⁻¹ := rfl
    rw [h1, map_mul, map_inv, hob, mul_inv_cancel_right]
    exact ho
  have hyC : k * (x : G)⁻¹ ∈ C := hC (mem_solvableRadical_of_mk_mem_oddCore hK₀H hy hyo)
  have hkeq : k = (k * (x : G)⁻¹) * x := by group
  rw [hkeq]
  exact Subgroup.mul_mem_sup ⟨hy, hyC⟩ hxKe

theorem nonQ_dichotomy
    (h3214 : Stmt3_2_14) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) {T K₀ Ke : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀) (hKe : Ke ∈ lFamily T)
    (hKeK₀ : Ke ≤ K₀) (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    K₀ ≤ (K₀ ⊓ centralizer (conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T) : Set G)) ⊔ Ke ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        IsSL2 p (↥(modO2Image (K₀ ⊔ T) K₀) ⧸ CFSG.oddCore ↥(modO2Image (K₀ ⊔ T) K₀)) := by
  have : IsSimpleGroup G := hs
  set H := K₀ ⊔ T with hH
  set P := CFSG.pCore 2 ↥H with hP
  have hK₀H : K₀ ≤ H := le_sup_left
  have hLocal : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hSQ : Vol2Native.SQTKHypCat (↥H ⧸ P) :=
    Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hLocal hK₀.2.2.2
  have hSH : IsSylowTwoOf T H := ⟨le_sup_right, hT.1, fun h2 => hT.2 (h2.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le
      (le_sup_right : T ≤ H)))⟩
  have hTbar : IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' P)) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSH) _
      (QuotientGroup.mk'_surjective P)
  have hK₀c : K₀ ∈ cComp H := hK₀.2.1
  have hLc : modO2Image H K₀ ∈ cComp (⊤ : Subgroup (↥H ⧸ P)) := modO2Image_mem_cComp hK₀c
  have hBl : modO2Image H Ke ∈ lFamily ((T.subgroupOf H).map (QuotientGroup.mk' P)) :=
    modO2Image_mem_lFamily hSH (hKeK₀.trans hK₀H) hKe
  have hBL : modO2Image H Ke ≤ modO2Image H K₀ := Subgroup.map_mono fun x hx => hKeK₀ hx
  have hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image H K₀) := by
    intro h
    obtain ⟨e⟩ := modO2_mulEquiv hK₀c
    exact hq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h)
  have h36 : A36Strong (modO2Image H K₀) :=
    (Vol2Native.a36CoreForSQTKCat_proved (↥H ⧸ P) hSQ _ hLc).toStrong hnq
  have hNQ := A312.nonquasi_of_lFamily a312SL2Fact hTbar hLc hBL hBl h36 hnq
  unfold A312Nonquasi at hNQ
  dsimp only at hNQ
  rcases hNQ with ⟨-, hLB, -⟩ | ⟨-, hp, -⟩
  · left
    exact le_sup_of_le_sup_oddCore hK₀H hKeK₀
      (solvableRadical_le_centralizer_conjClosure h3214 hs hnab hQ hT hK₀ hq) hLB.le
  · right
    exact hp

end CFSG.Quasithin.H13.A7
