module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisNorm
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisUpper
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisSylow
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpA
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

open CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_semidihedral_of_nonabelian (hd : Module.finrank (ZMod 2) V = 6)
    {Pb : Subgroup (GLV V)} (hPb : Nat.card Pb = 27) (hnc : ∃ u ∈ Pb, ∃ v ∈ Pb, u * v ≠ v * u)
    (hexp : ∀ g ∈ Pb, g ^ 3 = 1)
    (hirr : ∀ U : Submodule (ZMod 2) V, Invariant Pb U → U = ⊥ ∨ U = ⊤) :
    ∃ S₀ : Subgroup (GLV V), S₀ ≤ Subgroup.normalizer (Pb : Set (GLV V)) ∧ Nat.card S₀ = 16 ∧
      Nonempty (↥S₀ ≃* SemidihedralGroup 4) := by
  obtain ⟨u, hu, v, hv, huv⟩ := hnc
  have hncQ : ∃ a b : ↥Pb, a * b ≠ b * a :=
    ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv (congrArg Subtype.val h)⟩
  set z : GLV V := u * v * u⁻¹ * v⁻¹ with hz
  have hzP : z ∈ Pb := Pb.mul_mem (Pb.mul_mem (Pb.mul_mem hu hv) (Pb.inv_mem hu)) (Pb.inv_mem hv)
  have hzc : ∀ g ∈ Pb, g * z = z * g := by
    intro g hg
    have hcen := SmD6Grp.commutator_mem_center hPb hncQ ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨g, hg⟩)
  have hz1 : z ≠ 1 := by
    intro h1
    apply huv
    have : u * v * u⁻¹ * v⁻¹ = 1 := h1
    calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
      _ = v * u := by rw [this, one_mul]
  have hxy : u * v = z * v * u := by rw [hz]; group
  have hgen : ∀ g ∈ Pb, g ∈ Subgroup.closure ({u, v} : Set (GLV V)) := by
    intro g hg
    have h1 : (⟨g, hg⟩ : ↥Pb) ∈ Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩} : Set ↥Pb) := by
      rw [SmD6GrpB.closure_pair_eq_top hPb (fun h => huv (congrArg Subtype.val h))]
      trivial
    have h2 := Subgroup.mem_map_of_mem Pb.subtype h1
    rwa [MonoidHom.map_closure, Set.image_pair] at h2
  have hrel : PtRel u v z :=
    ptRel_of_group hirr hu hv (hexp u hu) (hexp v hv) (hexp z hzP) hz1 hzc hxy
  obtain ⟨B, hBx, hBy, hBz⟩ := exists_basis hd hirr hrel hgen
  exact exists_semidihedral_normalizer hu hv hzP hgen B hBx hBy hBz

theorem exists_sylow_semidihedral_of_core {Γ A : Subgroup (GLV V)}
    (hd : Module.finrank (ZMod 2) V = 6) (P : Subgroup ↥Γ) (hPn : P.Normal)
    (hPe : CFSG.IsExtraspecial 3 ↥P) (hPc : Nat.card P = 27) (hPx : ∀ x : ↥P, x ^ 3 = 1)
    (hPi : P.index ∣ 16) (hcore : Nat.card (pCoreOf 3 Γ) ≤ 27)
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant (pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤)
    (hAΓ : A ≤ Γ) (hAe : IsElemAbelian 2 A) (hAc : Nat.card A = 4) :
    ∃ S : Subgroup (GLV V),
      CFSG.QuasithinUnique.IsSylowTwoOf S (Subgroup.normalizer (P.map Γ.subtype : Set (GLV V))) ∧
      Nonempty (↥S ≃* SemidihedralGroup 4) ∧ Γ ≤ P.map Γ.subtype ⊔ S ∧
      ∃ E : Subgroup (GLV V), E ≤ S ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 ∧ E ≤ Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  set Pb : Subgroup (GLV V) := P.map Γ.subtype with hPb_def
  have hPb : Nat.card Pb = 27 := by
    rw [hPb_def, Subgroup.card_map_of_injective Γ.subtype_injective]
    exact hPc
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  have hPcore : Pb = pCoreOf 3 Γ := by
    have hle : P ≤ CFSG.pCore 3 ↥Γ := le_sSup ⟨hPn, hP3⟩
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hle) (by rw [hPb]; exact hcore)
  have hirr : ∀ U : Submodule (ZMod 2) V, Invariant Pb U → U = ⊥ ∨ U = ⊤ := by
    rw [hPcore]
    exact hs
  have hexp : ∀ g ∈ Pb, g ^ 3 = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    have h3 : p ^ 3 = 1 := congrArg Subtype.val (hPx ⟨p, hp⟩)
    show (p : GLV V) ^ 3 = 1
    rw [← Subgroup.coe_pow, h3]
    rfl
  have hncP : ∃ a b : ↥P, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZ : Subgroup.center ↥P = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact Subgroup.mem_center_iff.2 fun b => hcon b a
    have h1 := IsExtraspecial.center_order_p 3 ↥P
    rw [hZ, Subgroup.card_top, hPc] at h1
    omega
  have hnc : ∃ u ∈ Pb, ∃ v ∈ Pb, u * v ≠ v * u := by
    obtain ⟨a, b, hab⟩ := hncP
    refine ⟨Γ.subtype a, ⟨a, a.2, rfl⟩, Γ.subtype b, ⟨b, b.2, rfl⟩, fun h => hab ?_⟩
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨S₀, hS₀N, hS₀c, hS₀iso⟩ := exists_semidihedral_of_nonabelian hd hPb hnc hexp hirr
  have hUB : ∀ T : Subgroup (GLV V), IsPGroup 2 T → T ≤ Subgroup.normalizer (Pb : Set (GLV V)) →
      Nat.card T ∣ 16 := fun T hT hTN =>
    card_dvd_sixteen_of_normalizing_two_group hPb hnc hexp hirr hT hTN
  have hΓN : Γ ≤ Subgroup.normalizer (Pb : Set (GLV V)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro γ hγ _ ⟨p, hp, rfl⟩
    refine ⟨(⟨γ, hγ⟩ : ↥Γ) * p * (⟨γ, hγ⟩ : ↥Γ)⁻¹, hPn.conj_mem p hp ⟨γ, hγ⟩, rfl⟩
  have hA2 : IsPGroup 2 (A.subgroupOf Γ) :=
    IsPGroup.of_card (n := 2) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΓ).toEquiv, hAc]
      norm_num)
  obtain ⟨T, hAT, hT2, hTgen⟩ := exists_sylow_complement P hPc hPi hA2
  set Tm : Subgroup (GLV V) := T.map Γ.subtype
  have hTmΓ : Tm ≤ Γ := Subgroup.map_subtype_le T
  have hTm2 : IsPGroup 2 Tm := hT2.map Γ.subtype
  obtain ⟨S, hTS, hSyl, hSiso⟩ := exists_sylow_two_containing hS₀N hS₀c hS₀iso hUB hTm2
    (hTmΓ.trans hΓN)
  refine ⟨S, hSyl, hSiso, ?_, A, ?_, hAe, hAc, hAΓ⟩
  · intro γ hγ
    obtain ⟨p, hp, t, ht, hpt⟩ := hTgen ⟨γ, hγ⟩
    have hγeq : γ = (p : GLV V) * (t : GLV V) := congrArg Subtype.val hpt
    rw [hγeq]
    exact Subgroup.mul_mem_sup ⟨p, hp, rfl⟩ (hTS ⟨t, ht, rfl⟩)
  · intro a ha
    exact hTS ⟨⟨a, hAΓ ha⟩, hAT (Subgroup.mem_subgroupOf.2 ha), rfl⟩

end SmD6Heis

end CFSG.Quasithin.SzN31
