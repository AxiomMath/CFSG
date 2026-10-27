module

public import CFSG.Quasithin.Vol2.Ch10SecBCoord
public import CFSG.Quasithin.Vol2.Ch10SecABasicQuot

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def T1Inner (T L : Subgroup G) : Prop :=
  ∀ s ∈ T1 T L, ∃ x₀ ∈ L, ∀ x ∈ L, s * x * s⁻¹ * (x₀ * x * x₀⁻¹)⁻¹ ∈ pCoreOf 2 L

abbrev mkO2 (K : Subgroup G) (x : G) (hx : x ∈ K) : ↥K ⧸ CFSG.pCore 2 ↥K :=
  ((⟨x, hx⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)

omit [Finite G] in
theorem mk_eq_mk_iff {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    mkO2 K x hx = mkO2 K y hy ↔ x * y⁻¹ ∈ pCoreOf 2 K := by
  have h := SecA.mk_eq_one_iff (K := K) (⟨x, hx⟩ * (⟨y, hy⟩ : ↥K)⁻¹)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h
  exact h

omit [Finite G] in
theorem mkO2_mul {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    mkO2 K (x * y) (K.mul_mem hx hy) = mkO2 K x hx * mkO2 K y hy := rfl

omit [Finite G] in
theorem mkO2_inv {K : Subgroup G} {x : G} (hx : x ∈ K) :
    mkO2 K x⁻¹ (K.inv_mem hx) = (mkO2 K x hx)⁻¹ := rfl

abbrev D1 (T L : Subgroup G) : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
  ((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

theorem isSylowTwoOf_D1 {T L I : Subgroup G} (h : Hyp10 G T L I) : IsSylowTwoOf (D1 T L) ⊤ :=
  isSylowTwoOf_map_of_surjective (SecA.isSylowTwoOf_inf h.fsu.maximal.1) _
    (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem exists_inner_coord {T L : Subgroup G} (hinner : T1Inner T L)
    (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ) (hψ : (D1 T L).map ψ.toMonoidHom = L32.U3)
    {s : G} (hs : s ∈ T1 T L) : ∃ c : L32.Γ, L32.IsU c ∧ ∀ (x : G) (hx : x ∈ L),
      ψ (mkO2 L (s * x * s⁻¹) ((Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx)) =
        c * ψ (mkO2 L x hx) * c⁻¹ := by
  obtain ⟨x₀, hx₀, hx₀s⟩ := hinner s hs
  have key : ∀ (x : G) (hx : x ∈ L),
      mkO2 L (s * x * s⁻¹) ((Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx) =
        mkO2 L x₀ hx₀ * mkO2 L x hx * (mkO2 L x₀ hx₀)⁻¹ := by
    intro x hx
    rw [← mkO2_mul, ← mkO2_inv, ← mkO2_mul, mk_eq_mk_iff]
    exact hx₀s x hx
  have hsT : s ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs.1, hs.2⟩
  have hD : ∀ u ∈ L32.U3, ψ (mkO2 L x₀ hx₀) * u * (ψ (mkO2 L x₀ hx₀))⁻¹ ∈ L32.U3 := by
    intro u hu
    rw [← hψ] at hu ⊢
    obtain ⟨d, ⟨⟨d', hd'L⟩, hd'T, rfl⟩, rfl⟩ := hu
    have hsd : s * d' * s⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hsT d').mp hd'T
    refine ⟨mkO2 L (s * d' * s⁻¹) hsd.2, ⟨⟨_, hsd.2⟩, hsd, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [key d' hd'L, map_mul, map_mul, map_inv]
    rfl
  exact ⟨ψ (mkO2 L x₀ hx₀),
    L32.normalizer_U3_aux _ (fun u hu => hD u ((L32.mem_uList_iff u).mp hu)),
    fun x hx => by rw [key, map_mul, map_mul, map_inv]⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
