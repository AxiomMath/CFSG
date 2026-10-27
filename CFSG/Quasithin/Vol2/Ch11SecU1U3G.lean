module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3B
public import CFSG.Quasithin.Vol2.Ch11SecU1U3F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] {L : Subgroup G} {C : Type} [Group C]

theorem inf_centralizer_map_embU (ψ : C ≃* ↥L) (H : Subgroup C) :
    L ⊓ Subgroup.centralizer ((H.map (embU ψ) : Subgroup G) : Set G) =
      (Subgroup.centralizer (H : Set C)).map (embU ψ) := by
  ext y
  constructor
  · rintro ⟨hyL, hyC⟩
    obtain ⟨d, rfl⟩ := exists_embU_eq ψ hyL
    refine ⟨d, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, rfl⟩
    apply embU_injective ψ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hyC _ ⟨h, hh, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(ψ d).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hd h hh]

theorem centralizer_le_normalizer_inf (hLn : L.Normal) (y : G) :
    Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨hgL, hgy⟩
    exact ⟨hLn.conj_mem g hgL n,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hgy) (Subgroup.inv_mem _ hn)⟩
  · rintro ⟨hgL, hgy⟩
    have h1 := hLn.conj_mem _ hgL n⁻¹
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hgy) hn
    exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

theorem exists_equiv_zcU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (ψ : PSU3F p F ≃* ↥L)
    {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ ψ' : PSU3F p F ≃* ↥L, embU ψ' (zcU hF) = y := by
  obtain ⟨y', rfl⟩ := exists_embU_eq ψ hyL
  rw [orderOf_embU] at hy2
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_zcU hp2 hF hy2)
  refine ⟨(MulAut.conj g⁻¹).trans ψ, ?_⟩
  show embU ψ (g⁻¹ * zcU hF * g⁻¹⁻¹) = embU ψ y'
  rw [← hg]
  congr 1
  group

variable [Finite F]

theorem exists_levi_data_U3 (hp5 : 5 ≤ p) (hp4 : p % 4 = 1) (hF : Nat.card F = p ^ 2)
    (hLn : L.Normal) (ψ : PSU3F p F ≃* ↥L) {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup G, Y ≤ L ∧ Y ≤ Subgroup.centralizer ({y} : Set G) ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      Nonempty (↥Y ≃* SL(2, ZMod p)) ∧
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Y : Set G)) ∧
      ∀ x ∈ L, orderOf x = 2 → x * y = y * x → x ≠ y →
        ∀ s ∈ Y, ∀ c ∈ L ⊓ Subgroup.centralizer (Y : Set G), x ≠ s * c := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ', hψ'⟩ := exists_equiv_zcU hp2 hF ψ hyL hy2
  set f := embU ψ' with hf
  have hfinj : Function.Injective f := embU_injective ψ'
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set G) = (leviCU hF).map f := by
    rw [← hψ', inf_centralizer_embU, centralizer_zcU hp2 hF]
  set Y : Subgroup G := (leviSL hF).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set G),
      L ⊓ Subgroup.centralizer ({y} : Set G)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviCU hp5 hF]
  have hYC0 : Y ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCL]
    exact Subgroup.map_mono (leviSL_le_leviCU hF)
  have hCY : L ⊓ Subgroup.centralizer (Y : Set G) =
      (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f :=
    inf_centralizer_map_embU ψ' (leviSL hF)
  refine ⟨Y, hYC0.trans inf_le_left, hYC0.trans inf_le_right, ?_, ?_, ?_,
    fun x hxL hx2 hxy hxne s hs c hc hxsc => ?_⟩
  ·
    rw [hYcomm]
    exact CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
      (centralizer_le_normalizer_inf hLn y) (centralizer_le_normalizer_inf hLn y)
  ·
    exact ⟨((leviSL hF).equivMapOfInjective f hfinj).symm.trans (leviSLEquiv hF).symm⟩
  ·
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    have ha : (a : G) ∈ (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f := by
      rw [← hCY]
      exact a.2
    have hb : (b : G) ∈ (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f := by
      rw [← hCY]
      exact b.2
    obtain ⟨c, hc, hca⟩ := ha
    obtain ⟨d, hd, hdb⟩ := hb
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hca, ← hdb, ← map_mul, ← map_mul,
      comm_of_mem_centralizer_leviSL hp2 hF hc hd]
  ·
    have hxC : x ∈ L ⊓ Subgroup.centralizer ({y} : Set G) :=
      ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr hxy⟩
    rw [hCL] at hxC
    obtain ⟨x₀, hx₀, rfl⟩ := hxC
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    rw [hCY] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have hx₀2 : orderOf x₀ = 2 := by rw [← hx2, hf, orderOf_embU]
    have hx₀z : x₀ ≠ zcU hF := fun h => hxne (by rw [h, hψ'])
    rw [← map_mul] at hxsc
    exact ne_mul_of_involution hp2 hp4 hF hx₀ hx₀2 hx₀z hs₀ hc₀ (hfinj hxsc)

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
