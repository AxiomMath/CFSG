module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411R

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {s t : ↥S} {b : G}

theorem exists_mem_nor_not_mem {T R : Subgroup G} (hT : IsPGroup 2 T) (hRT : R ≤ T)
    (hne : ¬ T ≤ R) : ∃ x ∈ T ⊓ Nor R, x ∉ R := by
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hlt : R.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    intro x hx
    have : (⟨x, hx⟩ : ↥T) ∈ R.subgroupOf T := by rw [h]; trivial
    exact this
  have h2 := normalizerCondition_of_isNilpotent (G := ↥T) (R.subgroupOf T) hlt
  obtain ⟨⟨x, hxT⟩, hxn, hxnot⟩ := SetLike.exists_of_lt h2
  refine ⟨x, Subgroup.mem_inf.2 ⟨hxT, ?_⟩, hxnot⟩
  rw [Subgroup.mem_normalizer_iff] at hxn ⊢
  intro g
  constructor
  · intro hg
    exact (hxn ⟨g, hRT hg⟩).1 hg
  · intro hg
    have hgT : g ∈ T := by
      have h1 : x * g * x⁻¹ ∈ T := hRT hg
      have := mul_mem (mul_mem (inv_mem hxT) h1) hxT
      simpa [mul_assoc] using this
    exact (hxn ⟨g, hgT⟩).2 hg

theorem cen_conj_mem {H : Subgroup G} {n x : G} (hn : n ∈ Nor H) (hx : x ∈ CenS H) :
    n * x * n⁻¹ ∈ CenS H := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : n⁻¹ * h * n ∈ H := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * h * n)).2
    have h2 : n * (n⁻¹ * h * n) * n⁻¹ = h := by group
    rw [h2] at h1
    exact h1 hh
  have e1 : (n⁻¹ * h * n) * x = x * (n⁻¹ * h * n) := Subgroup.mem_centralizer_iff.1 hx _ hh'
  calc h * (n * x * n⁻¹) = n * ((n⁻¹ * h * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * h * n)) * n⁻¹ := by rw [e1]
    _ = n * x * n⁻¹ * h := by group

theorem nor_le_nor_cenS {H : Subgroup G} {n : G} (hn : n ∈ Nor H) : n ∈ Nor (CenS H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => cen_conj_mem hn hx
  · intro hx
    have := cen_conj_mem (inv_mem hn) hx
    simpa [mul_assoc] using this

section
variable (C : Ctx411 S e ψ s t b)
include C

theorem Ctx411.R_le_Rs : S ⊓ Op 2 (Cen (t : G)) ≤ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G))) :=
  fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, Subgroup.le_normalizer hx⟩

theorem Ctx411.Rs_le_nor_S {x : G}
    (hx : x ∈ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G)))) : x ∈ Nor S := by
  have := nor_le_nor_cenS (Subgroup.mem_inf.1 hx).2
  rwa [C.CR] at this

theorem Ctx411.y_mem_nor_R {y : G} (hyS : y ∈ Nor S) (hyt : y ∈ Cen (t : G)) :
    y ∈ Nor (S ⊓ Op 2 (Cen (t : G))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · exact fun hr => R_conj_mem (t := t) hyS hyt hr
  · intro hr
    have := R_conj_mem (t := t) (inv_mem hyS) (inv_mem hyt) hr
    simpa [mul_assoc] using this

theorem Ctx411.Rs_conj {y x : G} (hyS : y ∈ Nor S) (hyt : y ∈ Cen (t : G))
    (hx : x ∈ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G)))) :
    y * x * y⁻¹ ∈ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G))) := by
  obtain ⟨hxT, hxN⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_inf.2 ⟨S3.Op_conj_mem 2 (Subgroup.le_normalizer hyt) hxT,
    mul_mem (mul_mem (C.y_mem_nor_R hyS hyt) hxN) (inv_mem (C.y_mem_nor_R hyS hyt))⟩

theorem Ctx411.Rs_le_OpY :
    Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G))) ≤ Op 2 (Nor S ⊓ Cen (t : G)) := by
  refine S3.le_Op_of_normal 2 (Nor S ⊓ Cen (t : G)) _ ?_ ?_ ?_
  · intro x hx
    exact Subgroup.mem_inf.2 ⟨C.Rs_le_nor_S hx, S3.Op_le 2 _ (Subgroup.mem_inf.1 hx).1⟩
  · exact (S3.Op_isPGroup 2 _).to_le inf_le_left
  · intro h hh m hm
    exact C.Rs_conj (Subgroup.mem_inf.1 hh).1 (Subgroup.mem_inf.1 hh).2 hm

theorem Ctx411.psi_Rs_mem_E (n : ↥(Nor S))
    (hn : (n : G) ∈ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G)))) : ψ n ∈ Eτ :=
  psi_Op_le C.H C.het n (C.Rs_le_OpY hn)

theorem Ctx411.exists_Rs_not_S :
    ∃ x ∈ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G))), x ∉ S := by
  have hTR : ¬ Op 2 (Cen (t : G)) ≤ S ⊓ Op 2 (Cen (t : G)) := by
    intro hle
    apply C.not_S_le_T
    have hTS : Op 2 (Cen (t : G)) ≤ S := fun x hx => (Subgroup.mem_inf.1 (hle hx)).1
    intro x hx
    refine B_charTwo_cen C.hc (orderOf_t e C.ht1) (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (S_comm' e hx t.2)
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (S_comm' e hx (hTS hr)).symm
  obtain ⟨x, hx, hxn⟩ := exists_mem_nor_not_mem (S3.Op_isPGroup 2 _) inf_le_right hTR
  refine ⟨x, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩, ?_⟩
  intro hS
  exact hxn (Subgroup.mem_inf.2 ⟨hS, (Subgroup.mem_inf.1 hx).1⟩)

theorem Ctx411.psi_Rs_eq :
    ((Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G)))).subgroupOf (Nor S)).map ψ = Eτ := by
  set X : Subgroup OmG :=
    ((Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G)))).subgroupOf (Nor S)).map ψ with hXdef
  have hXE : X ≤ Eτ := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
    exact C.psi_Rs_mem_E n hn
  have hconj : ∀ g ∈ MulAction.stabilizer OmG tau0, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨y, hy⟩ := psiY_surj C.H C.het ⟨g, hg⟩
    have hyg : ψ ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩ = g := by
      have := congrArg Subtype.val hy
      exact this
    have hyS := (Subgroup.mem_inf.1 y.2).1
    have hyt := (Subgroup.mem_inf.1 y.2).2
    refine Subgroup.mem_map.2 ⟨⟨y.1, hyS⟩ * n * ⟨y.1, hyS⟩⁻¹, ?_, ?_⟩
    · have hn' : (n : G) ∈ Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G))) := hn
      rw [Subgroup.mem_subgroupOf]
      exact C.Rs_conj hyS hyt hn'
    · rw [map_mul, map_mul, map_inv, hyg]
  have hnorm : MulAction.stabilizer OmG tau0 ≤ Nor X := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconj g hg x hx
    · intro hx
      have := hconj g⁻¹ (inv_mem hg) _ hx
      simpa [mul_assoc] using this
  rcases (C.hPar qMinus_tau0 tau0_ne_zero).2.1 X hXE hnorm with h | h
  · exfalso
    obtain ⟨x, hx, hxS⟩ := C.exists_Rs_not_S
    have hxN : x ∈ Nor S := C.Rs_le_nor_S hx
    have hmem : ψ ⟨x, hxN⟩ ∈ X := Subgroup.mem_map.2 ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hxS ((C.H.psi_eq_one_iff _).1 hmem)
  · exact h

theorem Ctx411.card_R : Nat.card ↥(S ⊓ Op 2 (Cen (t : G))) = 32 := by
  have hperp := C.R_perp
  have e1 : Nat.card ↥(S ⊓ Op 2 (Cen (t : G))) =
      Nat.card ↥{v : F6 | polarMinus v tau0 = 0} := by
    refine Nat.card_congr
      { toFun := fun r => ⟨Multiplicative.toAdd (e ⟨r.1, (Subgroup.mem_inf.1 r.2).1⟩),
          (hperp _).1 (Subgroup.mem_inf.1 r.2).2⟩
        invFun := fun v => ⟨((e.symm (Multiplicative.ofAdd v.1) : ↥S) : G),
          Subgroup.mem_inf.2 ⟨(e.symm _).2, (hperp _).2 (by have hv : polarMinus v.1 tau0 = 0 := v.2; simpa using hv)⟩⟩
        left_inv := fun r => by
          apply Subtype.ext
          simp
        right_inv := fun v => by
          apply Subtype.ext
          simp }
  have e2 : Nat.card ↥{v : F6 | polarMinus v tau0 = 0} = 32 := by
    rw [Nat.card_coe_set_eq]
    have e : {v : F6 | polarMinus v tau0 = 0} =
        ↑(Finset.univ.filter fun v : F6 => polarMinus v tau0 = 0) := by
      ext v
      simp
    rw [e, Set.ncard_coe_finset]
    decide
  rw [e1, e2]

theorem Ctx411.card_Rs :
    Nat.card ↥(Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G)))) = 512 := by
  set Rs := Op 2 (Cen (t : G)) ⊓ Nor (S ⊓ Op 2 (Cen (t : G))) with hRs
  have hle : Rs ≤ Nor S := fun x hx => C.Rs_le_nor_S hx
  let ψR : ↥Rs →* OmG := ψ.comp (Subgroup.inclusion hle)
  have hker : ψR.ker = (S ⊓ Op 2 (Cen (t : G))).subgroupOf Rs := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hxS : (x : G) ∈ S := (C.H.psi_eq_one_iff ⟨x.1, hle x.2⟩).1 h
      exact Subgroup.mem_inf.2 ⟨hxS, (Subgroup.mem_inf.1 x.2).1⟩
    · intro h
      exact (C.H.psi_eq_one_iff ⟨x.1, hle x.2⟩).2 (Subgroup.mem_inf.1 h).1
  have hrange : ψR.range = Eτ := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact C.psi_Rs_mem_E ⟨x.1, hle x.2⟩ x.2
    · intro hg
      rw [← C.psi_Rs_eq] at hg
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
      exact ⟨⟨n.1, hn⟩, rfl⟩
  have hE : Nat.card Eτ = 16 := by
    have := (C.hPar qMinus_tau0 tau0_ne_zero).1.2
    show Nat.card ↥(Op 2 (MulAction.stabilizer OmG tau0)) = 16
    rw [this]
    norm_num
  have h1 := Subgroup.card_mul_index ψR.ker
  rw [Subgroup.index_ker, hrange, hE, hker] at h1
  have h2 : Nat.card ↥((S ⊓ Op 2 (Cen (t : G))).subgroupOf Rs) = 32 := by
    rw [← C.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.R_le_Rs).toEquiv
  rw [h2] at h1
  omega

end

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
