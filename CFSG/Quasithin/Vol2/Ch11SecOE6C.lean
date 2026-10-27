module

public import CFSG.Quasithin.Vol2.Ch11SecDO22
public import CFSG.Quasithin.H13.NQCoreP134Setup
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin

@[expose] noncomputable def charQuotHom {K : Type*} [Group K] (F : Subgroup K) [F.Characteristic] :
    MulAut K →* MulAut (K ⧸ F) where
  toFun α := QuotientGroup.congr _ _ α (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem charQuotHom_mk {K : Type*} [Group K] (F : Subgroup K) [F.Characteristic] (α : MulAut K)
    (k : K) : charQuotHom F α (QuotientGroup.mk k) = QuotientGroup.mk (α k) :=
  rfl

variable {G : Type} [Group G] [Finite G]

structure Setting (G : Type) [Group G] [Finite G] (T H K Y : Subgroup G) : Prop where
  loc : QuasithinUnique.LocalSQTK G
  sylow : quasithinIsSylowTwo T
  core : pCoreOf 2 H ≠ ⊥
  le : Y ⊔ T ≤ H
  comp : K ∈ cComp H
  norm : H ≤ Subgroup.normalizer (K : Set G)
  xi : IsXi T Y
  five : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card Y → 5 ≤ q

namespace Setting

variable {T H K Y : Subgroup G} (S : Setting G T H K Y)
include S

theorem YH : Y ≤ H := le_sup_left.trans S.le

theorem TH : T ≤ H := le_sup_right.trans S.le

theorem KH : K ≤ H := le_of_mem_cComp S.comp

theorem sylowIn : QuasithinUnique.IsSylowTwoOf T H :=
  isSylowTwoOf_of_quasithinIsSylowTwo S.sylow S.TH

theorem normal_subgroupOf : (K.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer S.KH).mpr S.norm

theorem normal_bar : (modO2Image H K).Normal :=
  S.normal_subgroupOf.map _ (QuotientGroup.mk'_surjective _)

theorem le_normalizer_of_comm (h : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  intro k hk
  have hkH := S.KH hk
  have hW : k ∈ Subgroup.normalizer ((pCoreOf 2 H ⊔ Y : Subgroup G) : Set G) := by
    have hle : (pCoreOf 2 H ⊔ Y).map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 H ⊔ Y := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨o, ho, rfl⟩
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hkH) o).mp ho)
      · rintro _ ⟨y, hy, rfl⟩
        have e : (MulAut.conj k).toMonoidHom y = (k * y * k⁻¹ * y⁻¹) * y := by
          simp [MulAut.conj_apply]
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (h k hk y hy)) (Subgroup.mem_sup_right hy)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
  have hY := S.xi.eq_oTwoUpper_sup S.sylow ⟨S.le, S.core⟩
  rw [hY]
  exact normalizer_le_normalizer_oTwoUpper _ hW

theorem le_normalizer_of_le_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpY : p ∣ Nat.card Y) {P : Subgroup G} (hSyl : IsSylowIn p P Y)
    (hc : modO2Image H P ≤
      Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  have := S.normal_bar
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set C := Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hC
  set Kc : Subgroup G := (C.comap π).map H.subtype with hKc
  have key : ∀ h ∈ H, ∀ g ∈ Kc, h * g * h⁻¹ ∈ Kc := by
    rintro h hh _ ⟨g', hg', rfl⟩
    refine ⟨⟨h, hh⟩ * g' * ⟨h, hh⟩⁻¹, ?_, by simp⟩
    have hg'C : π g' ∈ C := hg'
    show π (⟨h, hh⟩ * g' * ⟨h, hh⟩⁻¹) ∈ C
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.normal_centralizer (H := modO2Image H K)).conj_mem _ hg'C _
  have hHKc : H ≤ Subgroup.normalizer (Kc : Set G) := fun h hh => by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key h hh g, fun hg => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hg
    simpa [mul_assoc] using this
  have hPKc : P ≤ Kc := by
    intro x hx
    have hxH : x ∈ H := S.YH (hSyl.1 hx)
    exact ⟨⟨x, hxH⟩, hc ⟨⟨x, hxH⟩, hx, rfl⟩, rfl⟩
  have hYKc : Y ≤ Kc := by
    rw [H13.NQCore.cl_of_sylow S.xi hp2 hpY hSyl]
    exact conjClosure_le fun y hy z hz =>
      (Subgroup.mem_normalizer_iff.mp (hHKc (S.YH hy)) z).mp (hPKc hz)
  refine S.le_normalizer_of_comm fun k hk y hy => ?_
  obtain ⟨y', hy', rfl⟩ := hYKc hy
  have hkH := S.KH hk
  have hcomm := Subgroup.mem_centralizer_iff.mp hy' (π ⟨k, hkH⟩) ⟨⟨k, hkH⟩, hk, rfl⟩
  have h1 : π (⟨k, hkH⟩ * y' * ⟨k, hkH⟩⁻¹ * y'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [← SecD.pCoreOf_subgroupOf, Subgroup.mem_subgroupOf] at h2
  simpa using h2

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE6
