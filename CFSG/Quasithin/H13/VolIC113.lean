module

public import CFSG.Quasithin.H13.A5Inputs2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSplit

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
open CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

omit [Finite G] in
theorem sup_le_normalizer (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer hTN

theorem inf_centralizer_blockU_eq (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    (L ⊔ T) ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ T) :=
  C1.inf_centralizer_blockU_eq hL le_sup_left (sup_le_normalizer hTN)
    fun _ hg => C1.exists_pow_mem_of_mem_sup hT.2.1 hTN hg

theorem commutator_mem_blockU (hL : IsShort2 L) (hTN : T ≤ Subgroup.normalizer (L : Set G))
    {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) {l : G} (hl : l ∈ L) :
    q * l * q⁻¹ * l⁻¹ ∈ blockU L :=
  C1.commutator_mem_blockU_of_mem_blockQ hL
    (fun _ hl' => C1.commutator_mem_blockQ_of_mem_pCoreOf le_sup_left (sup_le_normalizer hTN)
      hq hl') l hl

theorem blockU_le_pCoreOf (hL : IsShort2 L) (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    blockU L ≤ pCoreOf 2 (L ⊔ T) :=
  (C1.blockU_le_blockQ hL).trans (C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans le_sup_left)
    (fun _ hg => C1.mem_normalizer_blockQ (sup_le_normalizer hTN hg)) (C1.blockQ_isPGroup L))

theorem inf_centralizer_le_pCoreOf (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (L : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  intro d hd
  have hUL : (blockU L : Set G) ⊆ (L : Set G) := fun u hu =>
    C1.blockQ_le L (C1.blockU_le_blockQ hL hu)
  have hdH : d ∈ (L ⊔ T) ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨Subgroup.mem_sup_right hd.1, Subgroup.centralizer_le hUL hd.2⟩
  rwa [inf_centralizer_blockU_eq hL hT hTN] at hdH

theorem pCoreOf_comm_blockU (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) {q u : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    (hu : u ∈ blockU L) : q * u = u * q := by
  have hqH : q ∈ (L ⊔ T) ⊓ Subgroup.centralizer (blockU L : Set G) := by
    rw [inf_centralizer_blockU_eq hL hT hTN]
    exact hq
  exact (Subgroup.mem_centralizer_iff.1 hqH.2 u hu).symm

theorem blockQ_comm_pCoreOf (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (h5 : IsAltType L 5) {q n : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hn : n ∈ blockQ L) : q * n = n * q := by
  have hqC : ∀ u ∈ blockU L, q * u = u * q := fun u hu => pCoreOf_comm_blockU hL hT hTN hq hu
  have hnL : n ∈ L := C1.blockQ_le L hn
  set e : G := q * n * q⁻¹ * n⁻¹ with he
  have heU : e ∈ blockU L := commutator_mem_blockU hL hTN hq hnL
  have hcent : ∀ ℓ ∈ L, ℓ * e * ℓ⁻¹ = e := by
    intro ℓ hℓ
    set c : G := q * ℓ * q⁻¹ * ℓ⁻¹ with hc
    have hcU : c ∈ blockU L := commutator_mem_blockU hL hTN hq hℓ
    set m : G := ℓ * n * ℓ⁻¹ with hm
    have hmQ : m ∈ blockQ L := conj_mem_blockQ hℓ hn
    set w : G := ℓ * e * ℓ⁻¹ with hw
    have hwU : w ∈ blockU L := conj_mem_blockU hℓ heU
    set u₁ : G := ℓ * n * ℓ⁻¹ * n⁻¹ with hu₁
    have hu₁U : u₁ ∈ blockU L := C1.commutator_mem_blockU' hℓ hn
    have h1 : q * ℓ * q⁻¹ = c * ℓ := by
      rw [hc]
      group
    have h2 : q * n * q⁻¹ = e * n := by
      rw [he]
      group
    have hcw : c * w = w * c := blockU_comm_blockU hL hcU hwU
    have hcm : c * m = m * c := C1.blockU_comm hL c hcU m hmQ
    have h3 : q * m * q⁻¹ = w * m := by
      calc q * m * q⁻¹ = (q * ℓ * q⁻¹) * (q * n * q⁻¹) * (q * ℓ * q⁻¹)⁻¹ := by
            rw [hm]
            group
        _ = (c * ℓ) * (e * n) * (c * ℓ)⁻¹ := by rw [h1, h2]
        _ = c * (ℓ * e * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) * c⁻¹ := by group
        _ = c * w * m * c⁻¹ := rfl
        _ = w * m := by
          rw [hcw, mul_assoc w c m, hcm]
          group
    have hmu : m = u₁ * n := by
      rw [hm, hu₁]
      group
    have hq1 : q * u₁ * q⁻¹ = u₁ := by
      rw [hqC u₁ hu₁U]
      group
    have heu : u₁ * e = e * u₁ := blockU_comm_blockU hL hu₁U heU
    have h4 : q * m * q⁻¹ = u₁ * e * n := by
      calc q * m * q⁻¹ = (q * u₁ * q⁻¹) * (q * n * q⁻¹) := by
            rw [hmu]
            group
        _ = u₁ * (e * n) := by rw [hq1, h2]
        _ = u₁ * e * n := by group
    have h5' : w * (u₁ * n) = u₁ * e * n := by rw [← hmu, ← h3, h4]
    have h6 : w * u₁ = u₁ * e := by
      have := h5'
      rw [← mul_assoc] at this
      exact mul_right_cancel this
    have hwu : w * u₁ = u₁ * w := blockU_comm_blockU hL hwU hu₁U
    rw [hwu] at h6
    exact mul_left_cancel h6
  have hZ : e ∈ blockZ L := ⟨heU, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => by
    have := hcent ℓ hℓ
    calc ℓ * e = (ℓ * e * ℓ⁻¹) * ℓ := by group
      _ = e * ℓ := by rw [this]⟩
  have hZ1 : e = 1 := by
    have := hZ
    rw [blockZ_eq_bot_of_alt5 hL h5] at this
    exact this
  have : q * n * q⁻¹ * n⁻¹ = 1 := hZ1
  calc q * n = (q * n * q⁻¹ * n⁻¹) * (n * q) := by group
    _ = n * q := by rw [this, one_mul]

theorem exists_split (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (h5 : IsAltType L 5) (P : A5Pi L) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    ∃ u ∈ blockU L, ∃ d ∈ T ⊓ Subgroup.centralizer (L : Set G), q = u * d := by
  classical
  let cU : ↥L → ↥(blockU L) := fun γ =>
    ⟨q * γ * q⁻¹ * (γ : G)⁻¹, commutator_mem_blockU hL hTN hq γ.2⟩
  let ρ : ↥L →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp P.α
  let W : ↥L → (Fin 5 → ZMod 2) := fun γ => (Multiplicative.toAdd (P.β (cU γ))).1
  have hcU_mul : ∀ a b : ↥L, cU (a * b) = cU a *
      ⟨(a : G) * (cU b : G) * (a : G)⁻¹, conj_mem_blockU a.2 (cU b).2⟩ := by
    intro a b
    apply Subtype.ext
    show q * ((a : G) * b) * q⁻¹ * ((a : G) * b)⁻¹ =
      (q * a * q⁻¹ * (a : G)⁻¹) * ((a : G) * (q * b * q⁻¹ * (b : G)⁻¹) * (a : G)⁻¹)
    group
  have hπρ : ∀ a : ↥L, P.π ⟨(a : G), Subgroup.le_normalizer a.2⟩ = ρ a := fun a =>
    P.hπα (a : G) a.2
  have hW : ∀ a b : ↥L, W (a * b) = W a + pact (ρ a) (W b) := by
    intro a b
    have h1 : P.β (cU (a * b)) = P.β (cU a) *
        P.β ⟨(a : G) * (cU b : G) * (a : G)⁻¹, conj_mem_blockU a.2 (cU b).2⟩ := by
      rw [hcU_mul, map_mul]
    have h2 := P.hcomp ⟨(a : G), Subgroup.le_normalizer a.2⟩ (cU b)
      ⟨(a : G) * (cU b : G) * (a : G)⁻¹, conj_mem_blockU a.2 (cU b).2⟩ rfl
    rw [hπρ a] at h2
    show (Multiplicative.toAdd (P.β (cU (a * b)))).1 =
      (Multiplicative.toAdd (P.β (cU a))).1 + pact (ρ a) (Multiplicative.toAdd (P.β (cU b))).1
    rw [h1, toAdd_mul, h2]
    rfl
  have hρ : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ γ, ρ γ = σ := by
    intro σ hσ
    obtain ⟨γ, hγ⟩ := P.hα (⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩ : alternatingGroup (Fin 5))
    exact ⟨γ, by simp only [ρ, MonoidHom.comp_apply, hγ]; rfl⟩
  have hρev : ∀ γ, Perm.sign (ρ γ) = 1 := fun γ => Equiv.Perm.mem_alternatingGroup.1 (P.α γ).2
  have hker : ∀ k, ρ k = 1 → W k = 0 := by
    intro k hk
    have hαk : P.α k = 1 := Subtype.ext hk
    have hk' : k ∈ P.α.ker := hαk
    rw [P.hαk] at hk'
    have hkQ : (k : G) ∈ blockQ L := (mem_pCore_iff_mem_blockQ k).1 hk'
    have hcomm := blockQ_comm_pCoreOf hL hT hTN h5 hq hkQ
    have hc1 : cU k = 1 := by
      apply Subtype.ext
      show q * (k : G) * q⁻¹ * (k : G)⁻¹ = 1
      rw [hcomm]
      group
    show (Multiplicative.toAdd (P.β (cU k))).1 = 0
    rw [hc1, map_one]
    rfl
  obtain ⟨w₀, hw₀, hcob⟩ := cocycle_coboundary ρ hρ hρev W hW hker
  have hw₀' : w₀ ∈ evenWeight 5 := (mem_evenWeight_iff w₀).2 hw₀
  set u₀ : ↥(blockU L) := P.β.symm (Multiplicative.ofAdd ⟨w₀, hw₀'⟩) with hu₀
  have hβu₀ : P.β u₀ = Multiplicative.ofAdd ⟨w₀, hw₀'⟩ := by
    rw [hu₀]
    simp
  have hu₀P : (u₀ : G) ∈ pCoreOf 2 (L ⊔ T) := blockU_le_pCoreOf hL hTN u₀.2
  refine ⟨((u₀⁻¹ : ↥(blockU L)) : G), (u₀⁻¹).2, (u₀ : G) * q, ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (hT.pCoreOf_le hu₀P) (hT.pCoreOf_le hq)
  · refine Subgroup.mem_centralizer_iff.2 fun γ hγ => ?_
    set g : ↥L := ⟨γ, hγ⟩ with hg
    have hvanish : u₀ * cU g * ⟨(g : G) * (u₀ : G) * (g : G)⁻¹, conj_mem_blockU hγ u₀.2⟩⁻¹ =
        1 := by
      apply P.β.injective
      rw [map_mul, map_mul, map_inv, map_one]
      apply Multiplicative.toAdd.injective
      have h2 := P.hcomp ⟨(g : G), Subgroup.le_normalizer g.2⟩ u₀
        ⟨(g : G) * (u₀ : G) * (g : G)⁻¹, conj_mem_blockU hγ u₀.2⟩ rfl
      rw [hπρ g, hβu₀] at h2
      rw [toAdd_mul, toAdd_mul, toAdd_inv, h2, hβu₀]
      apply Subtype.ext
      funext i
      have hc := congrFun (hcob g) i
      simp only [Pi.add_apply] at hc
      show w₀ i + W g i + -(pact (ρ g) w₀ i) = 0
      rw [hc]
      generalize w₀ i = a
      generalize pact (ρ g) w₀ i = b
      revert a b
      decide
    have hX : (u₀ : G) * (q * (γ : G) * q⁻¹ * (γ : G)⁻¹) *
        ((γ : G) * (u₀ : G) * (γ : G)⁻¹)⁻¹ = 1 := congrArg Subtype.val hvanish
    have h' : (u₀ : G) * q * γ * q⁻¹ * (u₀ : G)⁻¹ * (γ : G)⁻¹ = 1 := by
      rw [← hX]
      group
    have h'' : (u₀ : G) * q * γ * q⁻¹ * (u₀ : G)⁻¹ = γ := mul_inv_eq_one.1 h'
    calc (γ : G) * ((u₀ : G) * q) = ((u₀ : G) * q * γ * q⁻¹ * (u₀ : G)⁻¹) * ((u₀ : G) * q) := by
          rw [h'']
      _ = (u₀ : G) * q * γ := by group
  · show q = (u₀⁻¹ : ↥(blockU L)) * ((u₀ : G) * q)
    simp

theorem stmtC113c : A5.StmtC113c := by
  intro G _ _ L T hT hTN hL h5
  obtain ⟨P⟩ := nonempty_a5pi hL h5
  refine ⟨le_antisymm (fun q hq => ?_) (sup_le (blockU_le_pCoreOf hL hTN)
    (inf_centralizer_le_pCoreOf hL hT hTN)), ?_⟩
  · obtain ⟨u, hu, d, hd, rfl⟩ := exists_split hL hT hTN h5 P hq
    exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hd)
  · refine eq_bot_iff.2 fun x hx => ?_
    have hxZ : x ∈ blockZ L := ⟨hx.1, hx.2.2⟩
    rw [blockZ_eq_bot_of_alt5 hL h5] at hxZ
    exact hxZ

end CFSG.Quasithin.H13.VolI
