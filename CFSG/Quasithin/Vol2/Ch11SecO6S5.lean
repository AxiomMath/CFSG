module

public import CFSG.Quasithin.Vol2.Ch11SecO6S4
public import CFSG.Quasithin.Vol2.Ch11SecDFacts7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecG.Bar
open CFSG.Quasithin.Vol2.Ch11.O6
open scoped MatrixGroups

section Conj

variable {X : Type} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]

omit [Finite X] [Fact r.Prime] in
theorem actsScalar_one_of_comm_mem {n : X}
    (h : ∀ d ∈ CFSG.pCore r X, n * d * n⁻¹ * d⁻¹ ∈ frattiniIn (CFSG.pCore r X)) :
    ActsScalar r (MulAut.conj n) 1 := by
  intro d hd
  obtain ⟨c, hc, hce⟩ := h d hd
  have hnor : (frattini ↥(CFSG.pCore r X)).Normal := inferInstance
  refine ⟨(⟨d, hd⟩ : ↥(CFSG.pCore r X))⁻¹ * c * ⟨d, hd⟩, ?_, ?_⟩
  · have := hnor.conj_mem c hc (⟨d, hd⟩ : ↥(CFSG.pCore r X))⁻¹
    simpa using this
  · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply,
      pow_one]
    rw [show ((c : ↥(CFSG.pCore r X)) : X) = n * d * n⁻¹ * d⁻¹ from hce]
    group

end Conj

section NormL1



theorem factCase1NormL1_holds : FactCase1NormL1 := by
  intro G _ _ K L₁ N n hlist h1 hKperf hL₁K hperf ⟨F₄, _, _, hF₄, ⟨eL⟩⟩ hNK hKN hNL
  obtain ⟨p, hp, hp5', φK, hφKs, hφKk⟩ := h1
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by rcases hp5' with h | h <;> omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, hφs, hφk, -⟩ := exists_kBar_hom hφKs hφKk
  have hn : n = 2 := by
    rcases hlist with h | ⟨h, -⟩
    · exact (false_of_list2 h hp2 hφs).elim
    · exact h
  subst hn
  have hF₄' : Nat.card F₄ = 4 := by rw [hF₄]; norm_num
  have h60 := index_pCore_eq_sixty hF₄' eL
  have hD : Case1Data (KBar K) := case1Data_of_shape (shape_of_lists hlist hp2 hφs)
  have hOF : CFSG.oddCore (KBar K) = CFSG.fittingSubgroup (KBar K) := oddCore_eq hD
  have hKb : ⁅(⊤ : Subgroup (KBar K)), (⊤ : Subgroup (KBar K))⁆ = ⊤ := commutator_top_eq_top hKperf
  have h2p := two_ne_zero_zmod hp5
  have hcard4 : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  set F := CFSG.fittingSubgroup (KBar K) with hFdef
  have hmemF : ∀ x : KBar K, φ x = 1 → x ∈ F := fun x hx => by
    rw [← hOF, ← hφk]
    exact hx
  obtain ⟨s, hsL, hφs1, hsc, -⟩ := exists_s hp5 hφk hL₁K hperf h60
  have hsF : s ∉ F := fun h => by
    rw [← hOF, ← hφk, MonoidHom.mem_ker, hφs1] at h
    exact neg_one_ne_one h2p h
  have hs2 : s ^ 2 = 1 := by
    have h := eq_of_phi_eq hp5 hφk hL₁K hperf h60 (pow_mem hsL 2) (one_mem _)
      (by rw [map_pow, hφs1, neg_one_sq, map_one])
    exact h
  have hsc' : ∀ x : KBar K, x⁻¹ * (MulAut.conj s) x ∈ F := fun x => hmemF _ (by
    rw [MulAut.conj_apply, map_mul, map_mul, map_mul, map_inv, map_inv, hφs1,
      show (-1 : SL(2, ZMod p)) * φ x = φ x * -1 by rw [neg_one_mul, mul_neg_one]]
    group)
  obtain ⟨r, hr, hrF, hinv⟩ := exists_prime_inverts hD hKb hsF hsc'
    (by rw [hs2]; exact one_mem _) (e := 1) (by rw [pow_one, hs2])
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    have := hD.struct.2.1 r hr hrF
    omega
  have hna := exists_not_triv r hD hrF (Or.inl hKb)
  set Nb : Subgroup (KBar K) := (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    with hNb
  have hNn : (N.subgroupOf K).Normal := ⟨fun x hx k => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKN k.2) x).mp hx⟩
  have hNbn : Nb.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hNbL : ∀ y ∈ Nb, ∀ x ∈ l1Bar K L₁, y * x * y⁻¹ ∈ l1Bar K L₁ := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨y * x * y⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNL hy) x).mp hx
  have hM : ∀ m ∈ Nb, m ∈ F → ∀ x ∈ l1Bar K L₁, m * x = x * m := by
    intro m hm hmF x hx
    have h1 : m * x * m⁻¹ * x⁻¹ ∈ l1Bar K L₁ ⊓ CFSG.oddCore (KBar K) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (hNbL m hm x hx) (inv_mem hx), ?_⟩
      rw [hOF]
      have hc : x * m⁻¹ * x⁻¹ ∈ F := (CFSG.fittingSubgroup_normal).conj_mem _ (inv_mem hmF) x
      have e : m * x * m⁻¹ * x⁻¹ = m * (x * m⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem hmF hc
    rw [l1Bar_inf_oddCore hp5 hφk hL₁K hperf h60, Subgroup.mem_bot] at h1
    calc m * x = m * x * m⁻¹ * x⁻¹ * (x * m) := by group
      _ = x * m := by rw [h1, one_mul]
  have hNbF : Nb ≤ F := by
    by_contra hcon
    have hne : Nb.map φ ≠ ⊥ := by
      intro hbot
      apply hcon
      intro y hy
      apply hmemF
      have : φ y ∈ Nb.map φ := Subgroup.mem_map_of_mem φ hy
      rwa [hbot, Subgroup.mem_bot] at this
    obtain ⟨n₀, hn₀, hφn₀⟩ := neg_one_mem_of_normal hcard4 h2p (hNbn.map φ hφs) hne
    have h1n : ActsScalar r (MulAut.conj n₀) 1 := actsScalar_one_of_comm_mem fun d hd => by
      have hcN : n₀ * d * n₀⁻¹ * d⁻¹ ∈ Nb := by
        have h' : d * n₀⁻¹ * d⁻¹ ∈ Nb := hNbn.conj_mem _ (inv_mem hn₀) d
        have e : n₀ * d * n₀⁻¹ * d⁻¹ = n₀ * (d * n₀⁻¹ * d⁻¹) := by group
        rw [e]
        exact mul_mem hn₀ h'
      have hcP : n₀ * d * n₀⁻¹ * d⁻¹ ∈ CFSG.pCore r (KBar K) :=
        mul_mem ((CFSG.pCore_normal).conj_mem _ hd n₀) (inv_mem hd)
      have hcF : n₀ * d * n₀⁻¹ * d⁻¹ ∈ F := CFSG.pCore_le_fitting _ r hcP
      have hfix : (MulAut.conj s) (n₀ * d * n₀⁻¹ * d⁻¹) = n₀ * d * n₀⁻¹ * d⁻¹ := by
        rw [MulAut.conj_apply, ← hM _ hcN hcF s hsL, mul_inv_cancel_right]
      exact mem_frattiniIn_of_neg_of_fix hr2 hinv hcP hfix
    have hfF : n₀ * s⁻¹ ∈ F := hmemF _ (by rw [map_mul, map_inv, hφn₀, hφs1, mul_inv_cancel])
    have hfs : ActsScalar r (MulAut.conj (n₀ * s⁻¹)⁻¹) 1 := by
      rw [← actsTrivially_iff]
      exact fitting_acts_triv r (inv_mem hfF)
    have h1s : ActsScalar r (MulAut.conj s) 1 := by
      have h' := ActsScalar.mul r hfs h1n
      rw [← map_mul, one_mul] at h'
      have e : (n₀ * s⁻¹)⁻¹ * n₀ = s := by group
      rwa [e] at h'
    obtain ⟨x, y, hxy⟩ := hna
    apply hxy
    intro d hd
    exact mul_mem (inv_mem (le_frattiniIn_of_one_of_neg hr2 h1s hinv hd))
      (le_frattiniIn_of_one_of_neg hr2 h1s hinv
        ((CFSG.pCore_normal).conj_mem _ hd (x * y * x⁻¹ * y⁻¹)))
  have : Nb.Normal := hNbn
  set C := Subgroup.centralizer (Nb : Set (KBar K)) with hC
  have hLC : l1Bar K L₁ ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun m hm => hM m hm (hNbF hm) x hx
  have hCtop : C.map φ = ⊤ := by
    rcases le_center_or_eq_top_of_normal hcard4 ((inferInstance : C.Normal).map φ hφs) with
      h | h
    · exfalso
      have hle : (φ.comp (l1Map hL₁K)).range ≤ Subgroup.center SL(2, ZMod p) := by
        rintro _ ⟨l, rfl⟩
        exact h ⟨l1Map hL₁K l, hLC (l1Map_mem hL₁K l), rfl⟩
      have := Subgroup.card_le_of_le hle
      rw [(range_spec hp5 hφk hL₁K hperf h60).2, card_center h2p] at this
      omega
    · exact h
  have hCF : C ⊔ F = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc, hcx⟩ : φ x ∈ C.map φ := hCtop ▸ Subgroup.mem_top _
    have hcf : c⁻¹ * x ∈ F := hmemF _ (by rw [map_mul, map_inv, hcx, inv_mul_cancel])
    have e : x = c * (c⁻¹ * x) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hcf)
  have hCt : C = ⊤ := eq_top_of_sup_nilpotent hKb inferInstance hCF
  intro x hx
  have hxK := hNK hx
  refine mem_sectionCentralizer_of_aut (Subgroup.le_normalizer hxK) fun z => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have hxN : ((⟨x, hxK⟩ : ↥K) : KBar K) ∈ Nb :=
    ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hzC : ((k : KBar K)) ∈ C := hCt ▸ Subgroup.mem_top _
  have hcomm := Subgroup.mem_centralizer_iff.mp hzC _ hxN
  rw [aut_mk]
  have e : ((SecG.conjK K ⟨x, Subgroup.le_normalizer hxK⟩ k : ↥K) : KBar K) =
      ((⟨x, hxK⟩ : ↥K) : KBar K) * (k : KBar K) * ((⟨x, hxK⟩ : ↥K) : KBar K)⁻¹ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  rw [e, hcomm]
  group

end NormL1

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
