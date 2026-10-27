module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1MoreNineC
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

section ConjAct

variable {G : Type} [Group G] {U : Subgroup G}

theorem coe_conjAct_apply (g : Subgroup.normalizer (U : Set G)) (u : ↥U) :
    ((conjAct U g u : ↥U) : G) = g * u * (g : G)⁻¹ :=
  Setup.coe_conjAct_apply g u

theorem conjAct_eq_one_of_mem_centralizer (g : Subgroup.normalizer (U : Set G))
    (hg : (g : G) ∈ Subgroup.centralizer (U : Set G)) : conjAct U g = 1 := by
  ext u
  rw [coe_conjAct_apply, MulAut.one_apply]
  have h := Subgroup.mem_centralizer_iff.mp hg (u : G) u.2
  rw [← h, mul_inv_cancel_right]

theorem mem_normalizer_of_mem_centralizer {c : G} (hc : c ∈ Subgroup.centralizer (U : Set G)) :
    c ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have h := Subgroup.mem_centralizer_iff.mp hc n hn
    rw [← h, mul_inv_cancel_right]
    exact hn
  · intro hn
    have h := Subgroup.mem_centralizer_iff.mp hc _ hn
    have e : n = c * n * c⁻¹ := by
      calc n = c⁻¹ * ((c * n * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * n * c⁻¹)) := by rw [h]
        _ = c * n * c⁻¹ := by group
    rw [e]
    exact hn

theorem le_normalizer_centralizer {L : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    L ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  have key : ∀ l ∈ Subgroup.normalizer (U : Set G), ∀ c ∈ Subgroup.centralizer (U : Set G),
      l * c * l⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro l hl c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : l⁻¹ * u * l⁻¹⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hl) u).mp hu
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hu'
    calc u * (l * c * l⁻¹) = l * (l⁻¹ * u * l⁻¹⁻¹ * c) * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * u * l⁻¹⁻¹)) * l⁻¹ := by rw [h1]
      _ = l * c * l⁻¹ * u := by group
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key l (hLU hl) c hc, fun hc => ?_⟩
  have := key l⁻¹ (Subgroup.inv_mem _ (hLU hl)) _ hc
  simpa [mul_assoc] using this

theorem conjAct_mem_autOn_of_mem_sup {L : Subgroup G}
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (g : Subgroup.normalizer (U : Set G))
    (hg : (g : G) ∈ L ⊔ Subgroup.centralizer (U : Set G)) : conjAct U g ∈ autOn L U := by
  rw [sup_comm] at hg
  obtain ⟨c, hc, l, hl, hcl⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_centralizer hLU)).1 hg
  have hge : g = ⟨c, mem_normalizer_of_mem_centralizer hc⟩ * ⟨l, hLU hl⟩ := Subtype.ext hcl
  rw [hge, map_mul, conjAct_eq_one_of_mem_centralizer _ hc, one_mul]
  exact Setup.mem_autOn_iff.2 ⟨⟨l, hLU hl⟩, hl, rfl⟩

theorem conjAct_mem_autOn {L : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G)) {l : G}
    (hl : l ∈ L) : conjAct U ⟨l, hLU hl⟩ ∈ autOn L U :=
  Setup.mem_autOn_iff.2 ⟨⟨l, hLU hl⟩, hl, rfl⟩

end ConjAct

section Translate

variable {G : Type} [Group G] {U : Subgroup G} [IsMulCommutative ↥U]

theorem autOn_le_stabSub {Y Cg : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer ((U ⊓ Cg : Subgroup G) : Set G)) :
    autOn Y U ≤ stabSub (Cg.subgroupOf U) := by
  intro x hx u
  obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_conjAct_apply]
  have h1 := Subgroup.mem_normalizer_iff.mp (hY hgY) (u : G)
  have hgu : (g : G) * u * (g : G)⁻¹ ∈ U := by
    rw [← coe_conjAct_apply]
    exact (conjAct U g u).2
  constructor
  · intro h
    exact (h1.2 ⟨hgu, h⟩).2
  · intro h
    exact (h1.1 ⟨u.2, h⟩).2

theorem le_fixV_autOn {L Cg : Subgroup G} (hC : U ⊓ Cg ≤ Subgroup.centralizer (L : Set G)) :
    Cg.subgroupOf U ≤ fixV (autOn L U) := by
  intro u hu x hx
  obtain ⟨l, hl, rfl⟩ := Setup.mem_autOn_iff.1 hx
  apply Subtype.ext
  rw [coe_conjAct_apply]
  have h := Subgroup.mem_centralizer_iff.mp (hC ⟨u.2, hu⟩) (l : G) hl
  rw [h, mul_inv_cancel_right]

theorem commV_autOn_eq_top {L : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hcomm : ⁅U, L⁆ = U) : commV (autOn L U) = ⊤ :=
  CFSG.Quasithin.AutOn.commV_autOn_eq_top hLU hcomm

omit [IsMulCommutative ↥U] in
theorem irr_autOn {L Cg : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hirr : ∀ J : Subgroup G, U ⊓ Cg ≤ J → J ≤ U → L ≤ Subgroup.normalizer (J : Set G) →
      J = U ⊓ Cg ∨ J = U) :
    ∀ J : Subgroup ↥U, Cg.subgroupOf U ≤ J → (∀ k ∈ autOn L U, ∀ w ∈ J, k w ∈ J) →
      J = Cg.subgroupOf U ∨ J = ⊤ := by
  intro J hCJ hJ
  set J' : Subgroup G := J.map U.subtype with hJ'
  have hmemJ' : ∀ v : ↥U, (v : G) ∈ J' ↔ v ∈ J := fun v =>
    ⟨fun ⟨w, hw, hwv⟩ => (Subtype.ext hwv : w = v) ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
  have h1 : U ⊓ Cg ≤ J' := fun x hx => (hmemJ' ⟨x, hx.1⟩).2 (hCJ hx.2)
  have h2 : J' ≤ U := Subgroup.map_subtype_le J
  have hinv : ∀ l ∈ L, ∀ n ∈ J', l * n * l⁻¹ ∈ J' := by
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨_, hJ _ (conjAct_mem_autOn hLU hl) w hw, ?_⟩
    show ((conjAct U ⟨l, hLU hl⟩ w : ↥U) : G) = l * (w : G) * l⁻¹
    rw [coe_conjAct_apply]
  have h3 : L ≤ Subgroup.normalizer (J' : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hinv l hl n hn, fun hn => ?_⟩
    have := hinv l⁻¹ (L.inv_mem hl) _ hn
    simpa [mul_assoc] using this
  rcases hirr J' h1 h2 h3 with h | h
  · left
    ext v
    rw [← hmemJ', h, Subgroup.mem_subgroupOf]
    exact ⟨fun hv => hv.2, fun hv => ⟨v.2, hv⟩⟩
  · right
    rw [eq_top_iff]
    intro v _
    rw [← hmemJ', h]
    exact v.2

end Translate

end CFSG.Quasithin.InternalSec
