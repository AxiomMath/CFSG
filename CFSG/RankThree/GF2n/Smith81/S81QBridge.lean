module

public import CFSG.RankThree.GF2n.Smith81.S81D6Res
public import CFSG.RankThree.GF2n.Smith81.S81XD6Def
public import CFSG.RankThree.GF2n.Smith81.S81QIdeal

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X

section Hom

variable (K : Type) [Field K] [CharP K 2]

@[expose] def lamGToLam : ↥(LamG K) →* ↥(Lam K) :=
  ((e7Data_valid.minGroup K).subtype.comp (LamG K).subtype).codRestrict (Lam K) fun x => x.2

@[expose] def lamGHom : ↥(LamG K) →* (W K ≃ₗ[K] W K) :=
  ((vAut0 K).toMonoidHom.comp (resV0 K)).comp (lamGToLam K)

variable {K}

theorem lamGHom_induces (x : ↥(LamG K)) : IndW (x : Gp K) (lamGHom K x) := fun w =>
  resV0_induces (K := K) (lamGToLam K x) w

variable [Finite K]

theorem lamGHom_injective : Function.Injective (lamGHom K) := by
  intro x y h
  have h1 : resV0 K (lamGToLam K x) = resV0 K (lamGToLam K y) := (vAut0 K).injective h
  have h2 := resV0_injective h1
  have h3 := congrArg (fun l : ↥(Lam K) => (l : (Module.End K (V K))ˣ)) h2
  exact Subtype.ext (Subtype.ext h3)

theorem range_lamGHom : (lamGHom K).range = EAut0 K := by
  ext y
  rw [MonoidHom.mem_range, mem_EAut0_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : Gp K), x.2, lamGHom_induces x⟩
  · rintro ⟨g, hg, hy⟩
    refine ⟨⟨g, hg⟩, ?_⟩
    exact (lamGHom_induces ⟨g, hg⟩).unique hy

end Hom

section Roots

variable {K : Type} [Field K] [CharP K 2]

theorem xE_mem_LamG {β : Rt} (hβ : β ∈ Perp) (c : K) : xE β c ∈ LamG K := xu_mem_Lam hβ c

theorem Rd6_subset_Perp {β : Rt} (hβ : β ∈ Rd6) : β ∈ Perp := (mem_Rd6.1 hβ).1

theorem lamGHom_xE {β : Rt} (hβ : β ∈ Perp) (c : K) :
    lamGHom K ⟨xE β c, xE_mem_LamG hβ c⟩ = vAut0 K (xuWUnit hβ c) := by
  apply LinearEquiv.ext
  intro w
  apply emb_injective
  have h1 := lamGHom_induces (K := K) ⟨xE β c, xE_mem_LamG hβ c⟩ w
  have h2 := xuWUnit_induces hβ c w
  rw [h1, vAut0_apply, h2]
  rfl

theorem URge_le_LamG {S : Finset Rt} (hS : S ⊆ Rd6) : URge K S 1 ≤ LamG K := by
  intro g hg
  refine URge_induction (C := fun g => g ∈ LamG K) hg ?_ (one_mem _) (fun x y hx hy => mul_mem hx hy)
  intro α hα _ c
  exact xE_mem_LamG (Rd6_subset_Perp (hS hα)) c

theorem ULG_eq_URge : ULG K = URge K Rd6 1 := by
  apply le_antisymm
  · intro x hx
    have key : ∀ u : (Module.End K (V K))ˣ, u ∈ UL K → ∃ y : Gp K, (y : (Module.End K (V K))ˣ) = u ∧
        y ∈ URge K Rd6 1 := by
      intro u hu
      unfold UL at hu
      induction hu using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨β, hβ, hzero, hpos, c, rfl⟩ := hg
        have hβR : β ∈ Rd6 := mem_Rd6.2 ⟨⟨hβ, hzero⟩, hpos⟩
        exact ⟨xE β c, rfl, xE_mem_URge hβR (by have := (mem_Rd6.1 hβR).2; exact_mod_cast this) c⟩
      | one => exact ⟨1, rfl, one_mem _⟩
      | mul u v hu hv ihu ihv =>
        obtain ⟨y, hy, hyU⟩ := ihu
        obtain ⟨z, hz, hzU⟩ := ihv
        exact ⟨y * z, by rw [← hy, ← hz]; rfl, mul_mem hyU hzU⟩
      | inv u hu ihu =>
        obtain ⟨y, hy, hyU⟩ := ihu
        exact ⟨y⁻¹, by rw [← hy]; rfl, inv_mem hyU⟩
    obtain ⟨y, hy, hyU⟩ := key (x : (Module.End K (V K))ˣ) (mem_ULG.1 hx)
    have : y = x := Subtype.ext hy
    rw [← this]
    exact hyU
  · intro g hg
    refine URge_induction (C := fun g => g ∈ ULG K) hg ?_ (one_mem _) (fun x y hx hy => mul_mem hx hy)
    intro α hα hh c
    have hαP := mem_Rd6.1 hα
    exact Subgroup.subset_closure ⟨α, (perp_iff.1 hαP.1).1, hαP.1.2, hαP.2, c, rfl⟩

theorem URge_Rd6_le_LamG : URge K Rd6 1 ≤ LamG K := URge_le_LamG le_rfl

end Roots

section Images

variable (K : Type) [Field K] [CharP K 2]

@[expose] def rootOps (S : Finset Rt) : Set (W K ≃ₗ[K] W K) :=
  {g | ∃ β ∈ S, ∃ hβ : β ∈ Perp, ∃ c : K, g = vAut0 K (xuWUnit hβ c)}

@[expose] def posU0 : Subgroup (W K ≃ₗ[K] W K) := Subgroup.closure (rootOps K Rd6)

variable {K}

theorem rootOps_subset_EAut0 {S : Finset Rt} : rootOps K S ⊆ (EAut0 K : Set (W K ≃ₗ[K] W K)) := by
  rintro _ ⟨β, -, hβ, c, rfl⟩
  exact vAut0_xuWUnit_mem_EAut0 hβ c

theorem posU0_le_EAut0 : posU0 K ≤ EAut0 K := (Subgroup.closure_le _).2 rootOps_subset_EAut0

variable [Finite K]

theorem exists_lamGHom_mem_closure {S : Finset Rt} (hS : S ⊆ Rd6) {g : Gp K} (hg : g ∈ URge K S 1) :
    ∃ x : ↥(LamG K), (x : Gp K) = g ∧ lamGHom K x ∈ Subgroup.closure (rootOps K S) := by
  refine URge_induction (C := fun g => ∃ x : ↥(LamG K), (x : Gp K) = g ∧
    lamGHom K x ∈ Subgroup.closure (rootOps K S)) hg ?_ ?_ ?_
  · intro α hα _ c
    have hαP := Rd6_subset_Perp (hS hα)
    refine ⟨⟨xE α c, xE_mem_LamG hαP c⟩, rfl, ?_⟩
    rw [lamGHom_xE hαP c]
    exact Subgroup.subset_closure ⟨α, hα, hαP, c, rfl⟩
  · refine ⟨1, rfl, ?_⟩
    rw [map_one]
    exact one_mem _
  · rintro x y ⟨x', hx', hx2⟩ ⟨y', hy', hy2⟩
    refine ⟨x' * y', by rw [← hx', ← hy']; rfl, ?_⟩
    rw [map_mul]
    exact mul_mem hx2 hy2

theorem map_lamGHom_URge {S : Finset Rt} (hS : S ⊆ Rd6) :
    ((URge K S 1).subgroupOf (LamG K)).map (lamGHom K) = Subgroup.closure (rootOps K S) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hmem⟩ := exists_lamGHom_mem_closure hS (Subgroup.mem_subgroupOf.1 hx)
    have : x' = x := Subtype.ext hx'
    rw [← this]
    exact hmem
  · rw [Subgroup.closure_le]
    rintro _ ⟨β, hβS, hβ, c, rfl⟩
    refine ⟨⟨xE β c, xE_mem_LamG hβ c⟩, ?_, lamGHom_xE hβ c⟩
    exact Subgroup.mem_subgroupOf.2
      (xE_mem_URge hβS (by have := (mem_Rd6.1 (hS hβS)).2; exact_mod_cast this) c)

theorem posU0_eq_map : posU0 K = ((URge K Rd6 1).subgroupOf (LamG K)).map (lamGHom K) :=
  (map_lamGHom_URge le_rfl).symm

end Images

section Radicals

private theorem pos_of_coord_one_check : ∀ k : Fin 126,
    MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 →
    ((Tag.rootCertificate .E7).root k nodeA2 = 1 ∨ (Tag.rootCertificate .E7).root k nodeNu = 1) →
      0 < ht ((Tag.rootCertificate .E7).root k) := by
  decide +kernel

theorem pos_of_coord_one {γ : Rt} (hγ : γ ∈ Perp) (h : γ nodeA2 = 1 ∨ γ nodeNu = 1) : 0 < ht γ := by
  obtain ⟨hroot, hperp⟩ := hγ
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hroot
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact pos_of_coord_one_check ⟨k, by omega⟩ hperp h

variable {K : Type} [Field K] [CharP K 2]

theorem mem_Rn_iff {n : Fin (Tag.rank .E7)} {β : Rt} (hn : n = nodeA2 ∨ n = nodeNu) :
    β ∈ Rn (Pi.evalAddMonoidHom (fun _ => ℤ) n) Rd6 ↔ β ∈ Perp ∧ β n = 1 := by
  constructor
  · intro h
    obtain ⟨hR, h1⟩ := Finset.mem_filter.1 h
    exact ⟨Rd6_subset_Perp hR, h1⟩
  · rintro ⟨hP, h1⟩
    refine Finset.mem_filter.2 ⟨mem_Rd6.2 ⟨hP, pos_of_coord_one hP ?_⟩, h1⟩
    rcases hn with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr h1

theorem rootOps_Rn_A2 : rootOps K (Rn fA2 Rd6) = rootSet0 K := by
  ext g
  rw [mem_rootSet0_iff]
  constructor
  · rintro ⟨β, hβ, hβP, c, rfl⟩
    exact ⟨β, hβP, ((mem_Rn_iff (Or.inl rfl)).1 hβ).2, c, rfl⟩
  · rintro ⟨β, hβP, h1, c, rfl⟩
    exact ⟨β, (mem_Rn_iff (Or.inl rfl)).2 ⟨hβP, h1⟩, hβP, c, rfl⟩

theorem rootOps_Rn_Nu : rootOps K (Rn fNu Rd6) = rootSetν K := by
  ext g
  rw [mem_rootSetν_iff]
  constructor
  · rintro ⟨β, hβ, hβP, c, rfl⟩
    exact ⟨β, hβP, ((mem_Rn_iff (Or.inr rfl)).1 hβ).2, c, rfl⟩
  · rintro ⟨β, hβP, h1, c, rfl⟩
    exact ⟨β, (mem_Rn_iff (Or.inr rfl)).2 ⟨hβP, h1⟩, hβP, c, rfl⟩

variable [Finite K]

theorem map_lamGHom_URge_A2 :
    ((URge K (Rn fA2 Rd6) 1).subgroupOf (LamG K)).map (lamGHom K) = rootRad0 K := by
  rw [map_lamGHom_URge (Rn_subset _), rootOps_Rn_A2]
  rfl

theorem map_lamGHom_URge_Nu :
    ((URge K (Rn fNu Rd6) 1).subgroupOf (LamG K)).map (lamGHom K) = rootRadν K := by
  rw [map_lamGHom_URge (Rn_subset _), rootOps_Rn_Nu]
  rfl

end Radicals

end CFSG.RankThree.GF2n.Smith81.D6Spin
