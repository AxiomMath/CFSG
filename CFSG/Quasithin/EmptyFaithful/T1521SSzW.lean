module

public import CFSG.Quasithin.EmptyFaithful.T1521SSzAmb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockWreath
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJComm
public import CFSG.Quasithin.EmptyFaithful.T1521SAux
public import CFSG.Quasithin.EmptyFaithful.T1521SDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure WreathData1521 (X S L : Subgroup G) (t : G) : Prop where
  le : L ≤ X
  mem : t ∈ S
  memX : t ∈ X
  not_norm : t ∉ Subgroup.normalizer (L : Set G)
  orbits : conjSubgroupsBy X L = conjSubgroupsBy S L
  pair : conjSubgroupsBy S L = {L, conjByElt t L}
  inter : (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) = pCoreOf 2 X

namespace WreathData1521

variable {X S L : Subgroup G} {t : G} (hW : WreathData1521 X S L t)
include hW

theorem orbit_cases {x : G} (hx : x ∈ S) :
    x ∈ Subgroup.normalizer (L : Set G) ∨ t⁻¹ * x ∈ Subgroup.normalizer (L : Set G) := by
  have hmem : conjByElt x L ∈ conjSubgroupsBy S L := ⟨x, hx, rfl⟩
  rw [hW.pair] at hmem
  rcases hmem with h | h
  · exact Or.inl (GoldMLA.mem_normalizer_of_conjByElt_eq h)
  · refine Or.inr (GoldMLA.mem_normalizer_of_conjByElt_eq ?_)
    rw [GoldMLA.conjByElt_mul', h, ← GoldMLA.conjByElt_mul', inv_mul_cancel,
      GoldMLA.conjByElt_one']

theorem mul_self_mem_normalizer : t * t ∈ Subgroup.normalizer (L : Set G) := by
  rcases hW.orbit_cases (S.mul_mem hW.mem hW.mem) with h | h
  · exact h
  · exact absurd (by simpa using h) hW.not_norm

theorem normalizer_conj {x : G} (hx : x ∈ S) (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer ((conjByElt t L : Subgroup G) : Set G) := by
  have hmem : conjByElt (x * t) L ∈ conjSubgroupsBy S L := ⟨x * t, S.mul_mem hx hW.mem, rfl⟩
  rw [hW.pair] at hmem
  rcases hmem with h | h
  · exfalso
    apply hW.not_norm
    have hxt : x * t ∈ Subgroup.normalizer (L : Set G) :=
      GoldMLA.mem_normalizer_of_conjByElt_eq h
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hxt
    simpa using this
  · refine GoldMLA.mem_normalizer_of_conjByElt_eq ?_
    calc conjByElt x (conjByElt t L) = conjByElt (x * t) L := (GoldMLA.conjByElt_mul' x t L).symm
      _ = conjByElt t L := h

theorem conj_mem_normalizer {x : G} (hx : x ∈ S) (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    t⁻¹ * x * t ∈ Subgroup.normalizer (L : Set G) := by
  have h1 : conjByElt x (conjByElt t L) = conjByElt t L :=
    GoldMLA.conjByElt_eq_of_mem_normalizer (hW.normalizer_conj hx hxN)
  refine GoldMLA.mem_normalizer_of_conjByElt_eq ?_
  calc conjByElt (t⁻¹ * x * t) L = conjByElt t⁻¹ (conjByElt x (conjByElt t L)) := by
        rw [GoldMLA.conjByElt_mul', GoldMLA.conjByElt_mul']
    _ = conjByElt t⁻¹ (conjByElt t L) := by rw [h1]
    _ = L := by rw [← GoldMLA.conjByElt_mul', inv_mul_cancel, GoldMLA.conjByElt_one']

theorem le_normalizer : conjByElt t L ≤ Subgroup.normalizer (L : Set G) :=
  GoldMLA.conj_le_normalizer_of_orbits hW.le hW.memX hW.orbits hW.pair hW.not_norm

theorem le_normalizer' : L ≤ Subgroup.normalizer ((conjByElt t L : Subgroup G) : Set G) :=
  GoldMLA.le_normalizer_conj_of_orbits hW.le hW.memX hW.orbits hW.pair hW.not_norm

variable [Finite G]

theorem inf_central (hL : SzComponent1521 L) :
    ∀ x ∈ L ⊓ conjByElt t L, ∀ y ∈ L, x * y = y * x := by
  intro x hx
  have h1 : x ∈ pCoreOf 2 X := by
    have : x ∈ (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) :=
      ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩
    rwa [hW.inter] at this
  exact hL.pCoreOf_central (GoldMLA.inf_pCoreOf_le_pCoreOf hW.le ⟨h1, hx.1⟩)

theorem commute (hL : SzComponent1521 L) {l : G} (hl : l ∈ L) {l' : G}
    (hl' : l' ∈ conjByElt t L) : l * l' = l' * l := by
  have hN : ∀ x : G, x ∈ L → l' * x * l'⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hW.le_normalizer hl') x).mp hx
  have hN' : ∀ x : G, x ∈ L → x * l' * x⁻¹ ∈ conjByElt t L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hW.le_normalizer' hx) l').mp hl'
  have hc : ∀ x : ↥L, (x : G) * l' * (x : G)⁻¹ * l'⁻¹ ∈ L := by
    intro x
    have h1 := hN (x : G)⁻¹ (L.inv_mem x.2)
    have := L.mul_mem x.2 h1
    simpa [mul_assoc] using this
  have hcen : ∀ x : ↥L, ∀ y ∈ L, ((x : G) * l' * (x : G)⁻¹ * l'⁻¹) * y =
      y * ((x : G) * l' * (x : G)⁻¹ * l'⁻¹) := by
    intro x y hy
    refine hW.inf_central hL _ ⟨hc x, ?_⟩ y hy
    exact (conjByElt t L).mul_mem (hN' x x.2) ((conjByElt t L).inv_mem hl')
  have key := LJ.mem_of_perfect_central hL.quasi.1 (⊥ : Subgroup ↥L)
    (fun x : ↥L => (⟨(x : G) * l' * (x : G)⁻¹ * l'⁻¹, hc x⟩ : ↥L)) ?_ ?_ ⟨l, hl⟩
  · have h2 : l * l' * l⁻¹ * l'⁻¹ = 1 := by
      have := congrArg Subtype.val (Subgroup.mem_bot.mp key)
      simpa using this
    calc l * l' = (l * l' * l⁻¹ * l'⁻¹) * (l' * l) := by group
      _ = l' * l := by rw [h2, one_mul]
  · intro x y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · intro x
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hcen x g g.2).symm

omit hW [Finite G] in
theorem conj_mem_conjByElt' {b : G} (hb : b ∈ L) : t * b * t⁻¹ ∈ conjByElt t L := by
  rw [mem_conjByElt]
  have : t⁻¹ * (t * b * t⁻¹) * t = b := by group
  rwa [this]

theorem diag_conj_mem (hL : SzComponent1521 L)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1) {b : G}
    (hb : b ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) {x : G} (hx : x ∈ S) :
    (b * (t * b * t⁻¹)) * x * (b * (t * b * t⁻¹))⁻¹ ∈ S := by
  have hb'L' : t * b * t⁻¹ ∈ conjByElt t L := conj_mem_conjByElt' hb.1
  have hbi : t * b⁻¹ * t⁻¹ ∈ conjByElt t L := conj_mem_conjByElt' (L.inv_mem hb.1)
  have hcomm : b * (t * b⁻¹ * t⁻¹) = (t * b⁻¹ * t⁻¹) * b := hW.commute hL hb.1 hbi
  have first : ∀ y ∈ S, y ∈ Subgroup.normalizer (L : Set G) →
      b * ((t * b * t⁻¹) * y * (t * b * t⁻¹)⁻¹) * b⁻¹ ∈ S := by
    intro y hyS hyN
    have h1 : (t * b * t⁻¹) * y * (t * b * t⁻¹)⁻¹ ∈ S ⊓ Subgroup.normalizer (L : Set G) := by
      refine ⟨?_, ?_⟩
      · have hy' : t⁻¹ * y * t ∈ Subgroup.normalizer (L : Set G) :=
          hW.conj_mem_normalizer hyS hyN
        have hyS' : t⁻¹ * y * t ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hW.mem) hyS) hW.mem
        have h2 := (hL.conj_mem hP hS hb hyS' hy').1
        have h3 := S.mul_mem (S.mul_mem hW.mem h2) (S.inv_mem hW.mem)
        have e : (t * b * t⁻¹) * y * (t * b * t⁻¹)⁻¹ = t * (b * (t⁻¹ * y * t) * b⁻¹) * t⁻¹ := by
          group
        rw [e]
        exact h3
      · have hb'N : t * b * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := hW.le_normalizer hb'L'
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb'N hyN) (Subgroup.inv_mem _ hb'N)
    exact (hL.conj_mem hP hS hb h1.1 h1.2).1
  have e0 : ∀ y : G, (b * (t * b * t⁻¹)) * y * (b * (t * b * t⁻¹))⁻¹ =
      b * ((t * b * t⁻¹) * y * (t * b * t⁻¹)⁻¹) * b⁻¹ := fun y => by group
  rcases hW.orbit_cases hx with hxN | htx
  · rw [e0]
    exact first x hx hxN
  · have hmS : t⁻¹ * x ∈ S := S.mul_mem (S.inv_mem hW.mem) hx
    have hxm : x = t * (t⁻¹ * x) := by group
    have e1 : (b * (t * b * t⁻¹)) * x * (b * (t * b * t⁻¹))⁻¹ =
        ((b * (t * b * t⁻¹)) * t * (b * (t * b * t⁻¹))⁻¹) *
          ((b * (t * b * t⁻¹)) * (t⁻¹ * x) * (b * (t * b * t⁻¹))⁻¹) := by group
    have e2 : (b * (t * b * t⁻¹)) * t * (b * (t * b * t⁻¹))⁻¹ = b * (t * t) * b⁻¹ * t⁻¹ :=
      calc (b * (t * b * t⁻¹)) * t * (b * (t * b * t⁻¹))⁻¹
          = b * t * (b * (t * b⁻¹ * t⁻¹)) * b⁻¹ := by group
        _ = b * t * ((t * b⁻¹ * t⁻¹) * b) * b⁻¹ := by rw [hcomm]
        _ = b * (t * t) * b⁻¹ * t⁻¹ := by group
    rw [e1, e2, e0 (t⁻¹ * x)]
    refine S.mul_mem (S.mul_mem ?_ (S.inv_mem hW.mem)) (first _ hmS htx)
    exact (hL.conj_mem hP hS hb (S.mul_mem hW.mem hW.mem) hW.mul_self_mem_normalizer).1

theorem diag_mem_normalizer (hL : SzComponent1521 L)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1) {b : G}
    (hb : b ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    b * (t * b * t⁻¹) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hW.diag_conj_mem hL hP hS hb hx, fun hx => ?_⟩
  have hb' : b⁻¹ ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hb
  have h1 := hW.diag_conj_mem hL hP hS hb' hx
  have hbi : t * b⁻¹ * t⁻¹ ∈ conjByElt t L := conj_mem_conjByElt' (L.inv_mem hb.1)
  have hcomm : b⁻¹ * (t * b⁻¹ * t⁻¹) = (t * b⁻¹ * t⁻¹) * b⁻¹ :=
    hW.commute hL (L.inv_mem hb.1) hbi
  have e1 : (b * (t * b * t⁻¹))⁻¹ = b⁻¹ * (t * b⁻¹ * t⁻¹) := by
    calc (b * (t * b * t⁻¹))⁻¹ = (t * b⁻¹ * t⁻¹) * b⁻¹ := by group
      _ = b⁻¹ * (t * b⁻¹ * t⁻¹) := hcomm.symm
  have e2 : (b⁻¹ * (t * b⁻¹ * t⁻¹)) * ((b * (t * b * t⁻¹)) * x * (b * (t * b * t⁻¹))⁻¹) *
      (b⁻¹ * (t * b⁻¹ * t⁻¹))⁻¹ = x := by
    rw [← e1]
    group
  rw [e2] at h1
  exact h1

end WreathData1521

variable [Finite G]

theorem nrm1521_of_sz_wreath
    {X S L : Subgroup G} {t : G} (hW : WreathData1521 X S L t) (hL : SzComponent1521 L)
    (hP : IsSylowTwoOf (S ⊓ L) L) (hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1) : Nrm1521 S L := by
  set BL : Subgroup G := L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) with hBL
  set Δ : Subgroup G := Subgroup.closure {d | ∃ b ∈ BL, d = b * (t * b * t⁻¹)} with hΔ
  have hΔN : Δ ≤ Subgroup.normalizer (S : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hW.diag_mem_normalizer hL hP hS hb
  refine ⟨oTwoUpper Δ, ?_, ?_, oTwoUpper_oTwoUpper1521 Δ, ?_⟩
  · refine (oTwoUpper_le Δ).trans ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mul_mem _ (le_conjJoin hb) ?_
    exact Subgroup.mem_iSup_of_mem (⟨t, hW.mem⟩ : S) ⟨b, hb, by simp [MulAut.conj_apply]⟩
  · exact ((oTwoUpper_le Δ).trans hΔN).trans (normalizer_le_normalizer_thompsonJ S)
  · intro v hvS hvN hvB
    obtain ⟨s, hs, c, hc, rfl⟩ := hL.exists_mul hP hS hvS hvN
    refine hL.centralizes_of_forall_odd hP hs hc.2 ?_
    intro h hh hodd
    have hg : h⁻¹ ∈ BL := Subgroup.inv_mem _ hh
    have hgodd : Odd (orderOf h⁻¹) := by rwa [orderOf_inv]
    have hg'L' : t * h⁻¹ * t⁻¹ ∈ conjByElt t L := WreathData1521.conj_mem_conjByElt' hg.1
    have hd₁odd : Odd (orderOf (h⁻¹ * (t * h⁻¹ * t⁻¹))) := by
      refine hgodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
      rw [Commute.mul_pow (hW.commute hL hg.1 hg'L'), conj_pow, pow_orderOf_eq_one]
      simp
    have hd₁mem : h⁻¹ * (t * h⁻¹ * t⁻¹) ∈ oTwoUpper Δ :=
      mem_oTwoUpper_of_odd (Subgroup.subset_closure ⟨h⁻¹, hg, rfl⟩) hd₁odd
    have hvd := hvB _ hd₁mem
    have hcg : h⁻¹ * c = c * h⁻¹ := Subgroup.mem_centralizer_iff.mp hc.2 h⁻¹ hg.1
    have hv' : s * c ∈ Subgroup.normalizer ((conjByElt t L : Subgroup G) : Set G) :=
      hW.normalizer_conj hvS hvN
    have hBmem : (s * c) * (t * h⁻¹ * t⁻¹) * (s * c)⁻¹ ∈ conjByElt t L :=
      (Subgroup.mem_normalizer_iff.mp hv' _).mp hg'L'
    have hAmem : s * h⁻¹ * s⁻¹ ∈ L := L.mul_mem (L.mul_mem hs.2 hg.1) (L.inv_mem hs.2)
    have hAB : (s * h⁻¹ * s⁻¹) * ((s * c) * (t * h⁻¹ * t⁻¹) * (s * c)⁻¹) =
        h⁻¹ * (t * h⁻¹ * t⁻¹) := by
      have hA : s * h⁻¹ * s⁻¹ = (s * c) * h⁻¹ * (s * c)⁻¹ :=
        calc s * h⁻¹ * s⁻¹ = s * (c * h⁻¹ * c⁻¹) * s⁻¹ := by rw [← hcg]; group
          _ = (s * c) * h⁻¹ * (s * c)⁻¹ := by group
      rw [hA]
      calc (s * c) * h⁻¹ * (s * c)⁻¹ * ((s * c) * (t * h⁻¹ * t⁻¹) * (s * c)⁻¹)
          = (s * c) * (h⁻¹ * (t * h⁻¹ * t⁻¹)) * (s * c)⁻¹ := by group
        _ = h⁻¹ * (t * h⁻¹ * t⁻¹) := by rw [hvd]; group
    have hz : (s * h⁻¹ * s⁻¹)⁻¹ * h⁻¹ ∈ L ⊓ conjByElt t L := by
      refine ⟨L.mul_mem (L.inv_mem hAmem) hg.1, ?_⟩
      have e : (s * h⁻¹ * s⁻¹)⁻¹ * h⁻¹ =
          ((s * c) * (t * h⁻¹ * t⁻¹) * (s * c)⁻¹) * (t * h⁻¹ * t⁻¹)⁻¹ :=
        calc (s * h⁻¹ * s⁻¹)⁻¹ * h⁻¹
            = (s * h⁻¹ * s⁻¹)⁻¹ * (h⁻¹ * (t * h⁻¹ * t⁻¹)) * (t * h⁻¹ * t⁻¹)⁻¹ := by group
          _ = (s * h⁻¹ * s⁻¹)⁻¹ * ((s * h⁻¹ * s⁻¹) *
              ((s * c) * (t * h⁻¹ * t⁻¹) * (s * c)⁻¹)) * (t * h⁻¹ * t⁻¹)⁻¹ := by rw [hAB]
          _ = ((s * c) * (t * h⁻¹ * t⁻¹) * (s * c)⁻¹) * (t * h⁻¹ * t⁻¹)⁻¹ := by group
      rw [e]
      exact (conjByElt t L).mul_mem hBmem ((conjByElt t L).inv_mem hg'L')
    have hcent := hW.inf_central hL _ hz
    have e : ⁅s, h⁆ = (s * h⁻¹ * s⁻¹)⁻¹ * h⁻¹ := by rw [commutatorElement_def]; group
    rw [e, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcent y hy).symm

end CFSG.Quasithin
