module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.CatalogueBPrimeJoin
open CFSG.ComponentClassification.CatalogueBCentralQuotient
open scoped commutatorElement

section LemmaQ

variable {W W' : Type*} [Group W] [Group W']

theorem ggLemmaQ_commutator_le {E K : Subgroup W} [K.Normal] (hE : IsMulCommutative ↥E)
    (hEK : E ⊔ K = ⊤) (a b : W) : ⁅a, b⁆ ∈ K :=
  Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (N := K) (H := E) (by rw [sup_comm]; exact hEK) hE
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))

private theorem ggLemmaQ_commutator_mul_central {c₁ c₂ k l : W}
    (h1k : Commute c₁ k) (h1l : Commute c₁ l) (h2k : Commute c₂ k) (h2l : Commute c₂ l)
    (h12 : Commute c₁ c₂) : ⁅c₁⁻¹ * k, c₂⁻¹ * l⁆ = ⁅k, l⁆ := by
  have h2kl : Commute c₂ ⁅k, l⁆ := by
    rw [commutatorElement_def]
    exact (((h2k.mul_right h2l).mul_right h2k.inv_right).mul_right h2l.inv_right)
  have h1kl : Commute c₁ ⁅k, l⁆ := by
    rw [commutatorElement_def]
    exact (((h1k.mul_right h1l).mul_right h1k.inv_right).mul_right h1l.inv_right)
  have hc2 : c₂⁻¹ * ⁅k, l⁆ * c₂ = ⁅k, l⁆ := by
    rw [(h2kl.inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
  have hc1 : c₁⁻¹ * ⁅k, l⁆ * c₁ = ⁅k, l⁆ := by
    rw [(h1kl.inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [Commute.commutator_eq ((h12.inv_left.inv_right).mul_right h1l.inv_left), mul_one]
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [Commute.commutator_eq h2k.symm.inv_right, one_mul, inv_inv, inv_inv]
  rw [hc2, hc1]

theorem ggLemmaQ_commutator_fixed {K : Subgroup W} [K.Normal] {e k l : W} (hk : k ∈ K)
    (hl : l ∈ K) (hke : ⁅k, e⁆ ∈ Subgroup.centralizer (K : Set W))
    (hle : ⁅l, e⁆ ∈ Subgroup.centralizer (K : Set W)) : ⁅⁅k, l⁆, e⁆ = 1 := by
  have hc2K : ⁅l, e⁆ ∈ K := by
    have h : ⁅e, l⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem ((inferInstance : K.Normal).conj_mem l hl e) (K.inv_mem hl)
    simpa [commutatorElement_inv] using K.inv_mem h
  have h1k : Commute ⁅k, e⁆ k := (Subgroup.mem_centralizer_iff.mp hke k hk).symm
  have h1l : Commute ⁅k, e⁆ l := (Subgroup.mem_centralizer_iff.mp hke l hl).symm
  have h2k : Commute ⁅l, e⁆ k := (Subgroup.mem_centralizer_iff.mp hle k hk).symm
  have h2l : Commute ⁅l, e⁆ l := (Subgroup.mem_centralizer_iff.mp hle l hl).symm
  have h12 : Commute ⁅k, e⁆ ⁅l, e⁆ :=
    (Subgroup.mem_centralizer_iff.mp hke ⁅l, e⁆ hc2K).symm
  have hσk : MulAut.conj e k = ⁅k, e⁆⁻¹ * k := by
    rw [conj_eq_commutatorElement_mul, ← commutatorElement_inv k e]
  have hσl : MulAut.conj e l = ⁅l, e⁆⁻¹ * l := by
    rw [conj_eq_commutatorElement_mul, ← commutatorElement_inv l e]
  have hconj : MulAut.conj e ⁅k, l⁆ = ⁅k, l⁆ := by
    calc MulAut.conj e ⁅k, l⁆ = ⁅MulAut.conj e k, MulAut.conj e l⁆ :=
          map_commutatorElement (MulAut.conj e) k l
      _ = ⁅⁅k, e⁆⁻¹ * k, ⁅l, e⁆⁻¹ * l⁆ := by rw [hσk, hσl]
      _ = ⁅k, l⁆ := ggLemmaQ_commutator_mul_central h1k h1l h2k h2l h12
  have hcomm : Commute ⁅k, l⁆ e := by
    rw [commute_iff_eq]
    have h1 : e * ⁅k, l⁆ * e⁻¹ = ⁅k, l⁆ := by
      rw [← MulAut.conj_apply]; exact hconj
    have h2 : e * ⁅k, l⁆ = ⁅k, l⁆ * e := by
      have := congrArg (· * e) h1
      simpa [mul_assoc, inv_mul_cancel, mul_one] using this
    exact h2.symm
  exact hcomm.commutator_eq

theorem ggLemmaQ_le_image {K : Subgroup W} [K.Normal] (π : W →* W')
    (hπ : Function.Surjective π) (hcomm : ∀ a b : W, ⁅a, b⁆ ∈ K)
    (hker : π.ker ⊓ K ≤ Subgroup.centralizer (K : Set W)) (e : W) {C : Subgroup W'}
    (hC : ⁅C, C⁆ = C) (hCe : C ≤ Subgroup.centralizer {π e}) :
    C ≤ (K ⊓ Subgroup.centralizer {e}).map π := by
  let C' : Subgroup W := C.comap π
  let C1 : Subgroup W := K ⊓ C'
  have hC'map : C'.map π = C := Subgroup.map_comap_eq_self_of_surjective hπ C
  have hcommC' : ⁅C', C'⁆ ≤ K := Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  have hC'comm : ⁅C', C'⁆ ≤ C' := Subgroup.commutator_le_self C'
  have hC1upper : ⁅C', C'⁆ ≤ C1 := le_inf hcommC' hC'comm
  have hmapC1 : C1.map π = C := by
    apply le_antisymm
    · calc C1.map π ≤ C'.map π := Subgroup.map_mono inf_le_right
        _ = C := hC'map
    · calc C = ⁅C', C'⁆.map π := by rw [Subgroup.map_commutator, hC'map, hC]
        _ ≤ C1.map π := Subgroup.map_mono hC1upper
  have hC1comm_le : ⁅C1, C1⁆ ≤ K ⊓ Subgroup.centralizer {e} := by
    apply Subgroup.commutator_le.mpr
    intro k hk l hl
    have hkK : k ∈ K := hk.1
    have hlK : l ∈ K := hl.1
    have hpk : π k ∈ C := hk.2
    have hpl : π l ∈ C := hl.2
    have hck : Commute (π k) (π e) := Subgroup.mem_centralizer_singleton_iff.mp (hCe hpk)
    have hcl : Commute (π l) (π e) := Subgroup.mem_centralizer_singleton_iff.mp (hCe hpl)
    have hke_ker : ⁅k, e⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement (f := π)]
      exact Commute.commutator_eq hck
    have hle_ker : ⁅l, e⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement (f := π)]
      exact Commute.commutator_eq hcl
    have hke_cent : ⁅k, e⁆ ∈ Subgroup.centralizer (K : Set W) := hker ⟨hke_ker, hcomm k e⟩
    have hle_cent : ⁅l, e⁆ ∈ Subgroup.centralizer (K : Set W) := hker ⟨hle_ker, hcomm l e⟩
    have hfixed : ⁅⁅k, l⁆, e⁆ = 1 := ggLemmaQ_commutator_fixed hkK hlK hke_cent hle_cent
    exact ⟨hcomm k l,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_commute.mp hfixed).eq⟩
  have hC1map_comm : (⁅C1, C1⁆).map π = C := by
    rw [Subgroup.map_commutator, hmapC1, hC]
  calc C = (⁅C1, C1⁆).map π := hC1map_comm.symm
    _ ≤ (K ⊓ Subgroup.centralizer {e}).map π := Subgroup.map_mono hC1comm_le

variable [Finite W] (p : ℕ) [Fact p.Prime]

theorem ggLemmaQ_pComponent {K : Subgroup W} [K.Normal] (π : W →* W')
    (hπ : Function.Surjective π) (hcomm : ∀ a b : W, ⁅a, b⁆ ∈ K)
    (hker : π.ker ⊓ K ≤ Subgroup.centralizer (K : Set W)) (e : W) {C : Subgroup W'}
    (hCe : C ≤ Subgroup.centralizer {π e})
    (hC : CFSG.IsPComponent p (C.subgroupOf (Subgroup.centralizer {π e}))) :
    ∃ C₀ : Subgroup W, C₀ ≤ K ⊓ Subgroup.centralizer {e} ∧
      CFSG.IsPComponent p (C₀.subgroupOf (K ⊓ Subgroup.centralizer {e})) ∧ C₀.map π = C := by
  haveI : Finite W' := Finite.of_surjective (π : W → W') hπ
  let A : Subgroup W := K ⊓ Subgroup.centralizer {e}
  let Z : Subgroup W' := A.map π
  let f : ↥A →* ↥Z := imageRestriction π A
  have hf_surj : Function.Surjective f := imageRestriction_surjective π A
  haveI : Finite ↥Z := Finite.of_surjective (f : ↥A → ↥Z) hf_surj
  have hf_ker_central : f.ker ≤ Subgroup.center ↥A := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hyπ : π (y : W) = 1 := by
      have h2 : ((f y : ↥Z) : W') = 1 := by
        rw [MonoidHom.mem_ker.mp hy]; rfl
      rwa [show ((f y : ↥Z) : W') = π (y : W) from imageRestriction_apply π A y] at h2
    have hycent : (y : W) ∈ Subgroup.centralizer (K : Set W) := hker ⟨hyπ, y.property.1⟩
    exact Subgroup.mem_centralizer_iff.mp hycent (z : W) z.property.1
  have hCperf : ⁅C, C⁆ = C := ggPComponent_commutator_eq (p := p) hCe hC
  have hCZ : C ≤ Z := ggLemmaQ_le_image (K := K) π hπ hcomm hker e hCperf hCe
  have hZY : Z ≤ Subgroup.centralizer {π e} := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp ha.2])
  have hM : CFSG.IsPComponent p (C.subgroupOf Z) :=
    ggPComponent_subgroupOf_of_le (p := p) hCZ hZY hC
  let C1 : Subgroup ↥A := derivedPreimage f (C.subgroupOf Z)
  have hC1 : CFSG.IsPComponent p C1 :=
    pComponent_derivedPreimage p f hf_surj hf_ker_central (C.subgroupOf Z) hM
  haveI : Group.IsPerfect (C.subgroupOf Z) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hM
  refine ⟨C1.map A.subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.property
  · rw [show (C1.map A.subtype).subgroupOf A = C1 from
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective C1]
    exact hC1
  · have hcomp : π.comp A.subtype = Z.subtype.comp f := by
      ext x
      simpa [f] using (imageRestriction_apply π A x).symm
    have hC1map : C1.map f = C.subgroupOf Z := derivedPreimage_map f hf_surj (C.subgroupOf Z)
    calc (C1.map A.subtype).map π
        = C1.map (π.comp A.subtype) := Subgroup.map_map C1 π A.subtype
      _ = C1.map (Z.subtype.comp f) := by rw [hcomp]
      _ = (C1.map f).map Z.subtype := (Subgroup.map_map C1 Z.subtype f).symm
      _ = (C.subgroupOf Z).map Z.subtype := by rw [hC1map]
      _ = C := Subgroup.map_subgroupOf_eq_of_le hCZ

end LemmaQ

section Ambient

variable {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] {W E K : Subgroup X}
  {W' : Type*} [Group W']

theorem ggLemmaQ_ambient (π : ↥W →* W') (hπ : Function.Surjective π) (hW : E ⊔ K = W)
    (hKn : (K.subgroupOf W).Normal) (hE : IsMulCommutative ↥E)
    (hker : ∀ w : ↥W, π w = 1 → (w : X) ∈ K → (w : X) ∈ Subgroup.centralizer (K : Set X))
    (e : ↥W) {C : Subgroup W'} (hCe : C ≤ Subgroup.centralizer {π e})
    (hC : CFSG.IsPComponent p (C.subgroupOf (Subgroup.centralizer {π e}))) :
    ∃ C₀ : Subgroup X, C₀ ≤ K ⊓ Subgroup.centralizer {(e : X)} ∧
      CFSG.IsPComponent p (C₀.subgroupOf (K ⊓ Subgroup.centralizer {(e : X)})) ∧
      (C₀.subgroupOf W).map π = C := by
  haveI : (K.subgroupOf W).Normal := hKn
  have hEW : E ≤ W := hW ▸ le_sup_left
  have hKW : K ≤ W := hW ▸ le_sup_right
  have hE' : IsMulCommutative ↥(E.subgroupOf W) :=
    IsMulCommutative.of_comm fun a b => by
      apply (Subgroup.subgroupOfEquivOfLe hEW).injective
      simp only [map_mul]
      exact mul_comm' _ _
  have hE'K' : E.subgroupOf W ⊔ K.subgroupOf W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hEW hKW, hW, Subgroup.subgroupOf_self]
  have hcomm' : ∀ a b : ↥W, ⁅a, b⁆ ∈ K.subgroupOf W :=
    ggLemmaQ_commutator_le hE' hE'K'
  have hker' : π.ker ⊓ K.subgroupOf W ≤
      Subgroup.centralizer (K.subgroupOf W : Set ↥W) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (hker w (MonoidHom.mem_ker.mp hw.1) hw.2) (z : X) hz
  obtain ⟨C0', hC0'_le, hC0'_pcomp, hC0'_map⟩ :=
    ggLemmaQ_pComponent p (K := K.subgroupOf W) π hπ hcomm' hker' e hCe hC
  have hmap_inf : (K.subgroupOf W ⊓ Subgroup.centralizer {e}).map W.subtype
      = K ⊓ Subgroup.centralizer {(e : X)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      obtain ⟨hyK, hycent⟩ := Subgroup.mem_inf.mp hy
      rw [← hyx]
      refine Subgroup.mem_inf.mpr ⟨hyK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp hycent
      simpa using congrArg Subtype.val h2
    · intro hx
      obtain ⟨hxK, hxcent⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hKW hxK⟩, Subgroup.mem_inf.mpr ⟨hxK, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hxcent
  refine ⟨C0'.map W.subtype, ?_, ?_, ?_⟩
  · calc C0'.map W.subtype ≤ (K.subgroupOf W ⊓ Subgroup.centralizer {e}).map W.subtype :=
          Subgroup.map_mono hC0'_le
      _ = K ⊓ Subgroup.centralizer {(e : X)} := hmap_inf
  · have h := ggPComponent_map_subtype (p := p) (W := W) (A := C0')
        (B := K.subgroupOf W ⊓ Subgroup.centralizer {e}) hC0'_le hC0'_pcomp
    rwa [hmap_inf] at h
  · have hsub : (C0'.map W.subtype).subgroupOf W = C0' :=
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective C0'
    rw [hsub, hC0'_map]

end Ambient

end CFSG.StandardType
