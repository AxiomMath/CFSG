module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem23B
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22S

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem22

theorem L3_transitive : ∀ a b : L3.Vec, a ≠ 0 → b ≠ 0 → ∃ γ : L3.Γ, L3.act γ a = b := by
  unfold L3.act
  decide +kernel

variable {G : Type} [Group G] [Finite G]

abbrev yY (L V H P : Subgroup G) : Subgroup G := conjClosure (rR V H P) L

theorem le_normalizer_conjClosure (X K : Subgroup G) :
    K ≤ Subgroup.normalizer ((conjClosure X K : Subgroup G) : Set G) := by
  intro g hg
  refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
  have hle : conjClosure X K ≤ (conjClosure X K).comap (MulAut.conj g).toMonoidHom := by
    unfold conjClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show g * (k * x * k⁻¹) * g⁻¹ ∈ _
    exact Subgroup.subset_closure ⟨g * k, K.mul_mem hg hk, x, hx, by group⟩
  have h1 := hle hy
  rw [Subgroup.mem_comap] at h1
  exact h1

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem exists_conj_eq (e : Extra3 T L V H P U I h) {v w : G} (hv : v ∈ V) (hw : w ∈ V)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ l ∈ L, l * v * l⁻¹ = w := by
  obtain ⟨-, -, -, ⟨hcommV, hnatV⟩, -⟩ := e.concl
  obtain ⟨DV⟩ := hnatV.toL3Coord
  have hne : ∀ x : ↥V, (x : G) ≠ 1 →
      Multiplicative.toAdd (DV.β ⟨x, Subgroup.mem_top _⟩) ≠ 0 := by
    intro x hx h0
    apply hx
    have h1 : DV.β ⟨x, Subgroup.mem_top _⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this
    have h2 := (DV.ker_β _).mp h1
    rw [Subgroup.mem_bot] at h2
    exact congrArg Subtype.val h2
  obtain ⟨γ, hγ⟩ := L3_transitive _ _ (hne ⟨v, hv⟩ hv1) (hne ⟨w, hw⟩ hw1)
  obtain ⟨⟨l, hlN⟩, hl, hlγ⟩ := DV.rho_mem γ
  replace hl : l ∈ L := Subgroup.mem_subgroupOf.mp hl
  refine ⟨l, hl, ?_⟩
  have h1 := DV.β_rho γ (⟨v, hv⟩ : ↥V) (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [hγ] at h1
  have h2 : DV.β ⟨DV.rho γ ⟨v, hv⟩, Subgroup.mem_top _⟩ = DV.β ⟨⟨w, hw⟩, Subgroup.mem_top _⟩ := by
    rw [h1]
    simp
  have h3 := (l3_β_eq_iff DV _ _).mp h2
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h3
  have h4 := congrArg Subtype.val h3
  rw [← hlγ] at h4
  exact h4

theorem centralizer_le_CT
    (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  obtain ⟨-, hcard, htop, ⟨hcommV, -⟩, -⟩ := e.concl
  obtain ⟨hQLT, -⟩ := e.QL_facts h1222
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 e.hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcommV.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨ev⟩ := Lem24.nonempty_coords hVc hV2 hcard
  have hle := Lem24.centralizer_le_pCoreOf e.hyp hred (n := 3) (by norm_num) ev htop
  exact fun x hx => ⟨hQLT (hle hx), hx.2⟩

theorem L_le_normalizer_CT
    (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    L ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := e.hyp.irrPlus.2.2.1
  have hC := e.centralizer_le_CT h1222
  intro l hl
  refine Sec121Swap.mem_normalizer_of_conj_mem fun q hq => ?_
  have hlq : l * q * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer hLV hl) q).mp hq.2
  have hcomm : l * q * l⁻¹ * q⁻¹ ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨?_, Subgroup.mul_mem _ hlq (Subgroup.inv_mem _ hq.2)⟩
    have h1 : q * l⁻¹ * q⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (e.hyp.normalizes hq.1) l⁻¹).mp (L.inv_mem hl)
    have e1 : l * q * l⁻¹ * q⁻¹ = l * (q * l⁻¹ * q⁻¹) := by group
    rw [e1]
    exact L.mul_mem hl h1
  have e2 : l * q * l⁻¹ = (l * q * l⁻¹ * q⁻¹) * q := by group
  rw [e2]
  exact Subgroup.mul_mem _ (hC hcomm) hq

theorem yY_le_CT
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) : yY L V H P ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  have hLQ := e.L_le_normalizer_CT h1222
  refine conjClosure_le fun l hl r hr => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hLQ hl) r).mp ⟨e.rR_le_T h331 hr, hr.2⟩

theorem V_le_yY (e : Extra3 T L V H P U I h) : V ≤ yY L V H P := by
  have hV₀1 : V ⊓ pCoreOf 2 H ≠ ⊥ := fun h0 => by
    have h1 := e.card_inf
    rw [h0, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀1
  have hu1' : u ≠ 1 := fun h0 => hu1 (Subtype.ext h0)
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact Subgroup.one_mem _
  obtain ⟨l, hl, hlw⟩ := e.exists_conj_eq hu.1 hw hu1' hw1
  rw [← hlw]
  exact Subgroup.subset_closure ⟨l, hl, u, e.V0_le_rR hu, rfl⟩

theorem comm_yY_CT
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) :
    ∀ y ∈ yY L V H P, ∀ q ∈ T ⊓ Subgroup.centralizer (V : Set G), q * y * q⁻¹ * y⁻¹ ∈ V := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := e.hyp.irrPlus.2.2.1
  have hLQ := e.L_le_normalizer_CT h1222
  have hYQ := e.yY_le_CT h331 h1222
  have hRQ := e.comm_rR_CT h331 h1222
  intro y hy
  have key : y ∈ yY L V H P ∧
      ∀ q ∈ T ⊓ Subgroup.centralizer (V : Set G), q * y * q⁻¹ * y⁻¹ ∈ V := by
    unfold yY conjClosure at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, r, hr, rfl⟩ := hx
      refine ⟨Subgroup.subset_closure ⟨l, hl, r, hr, rfl⟩, fun q hq => ?_⟩
      have hq' : l⁻¹ * q * l ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
        have := (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hl)) q).mp hq
        simpa using this
      have h1 := hRQ r hr _ hq'
      have e1 : q * (l * r * l⁻¹) * q⁻¹ * (l * r * l⁻¹)⁻¹ =
          l * ((l⁻¹ * q * l) * r * (l⁻¹ * q * l)⁻¹ * r⁻¹) * l⁻¹ := by group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp h1.1
    | one => exact ⟨Subgroup.one_mem _, fun q _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, fun q hq => ?_⟩
      have h1 := iha.2 q hq
      have h2 := ihb.2 q hq
      have haT : a ∈ T := (hYQ iha.1).1
      have e1 : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
          (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
      rw [e1]
      exact V.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp (hTV haT) _).mp h2)
    | inv a _ iha =>
      refine ⟨Subgroup.inv_mem _ iha.1, fun q hq => ?_⟩
      have h1 := iha.2 q hq
      have haT : a ∈ T := (hYQ iha.1).1
      have e1 : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a := by group
      rw [e1]
      have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem haT)) _).mp (V.inv_mem h1)
      simpa using this
  exact key.2

theorem sq_yY
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) : ∀ y ∈ yY L V H P, y * y ∈ V := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hYQ := e.yY_le_CT h331 h1222
  have hcomm := e.comm_yY_CT h331 h1222
  obtain ⟨-, hR2⟩ := e.rR_elem h1222
  intro y hy
  have key : y ∈ yY L V H P ∧ y * y ∈ V := by
    unfold yY conjClosure at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, r, hr, rfl⟩ := hx
      refine ⟨Subgroup.subset_closure ⟨l, hl, r, hr, rfl⟩, ?_⟩
      have h1 : r * r = 1 := by rw [← pow_two]; exact hR2 r hr
      have e1 : l * r * l⁻¹ * (l * r * l⁻¹) = l * (r * r) * l⁻¹ := by group
      rw [e1, h1, mul_one, mul_inv_cancel]
      exact V.one_mem
    | one => exact ⟨Subgroup.one_mem _, by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, ?_⟩
      have hc := hcomm a iha.1 b (hYQ ihb.1)
      have haT : a ∈ T := (hYQ iha.1).1
      have e1 : a * b * (a * b) =
          (a * (b * a * b⁻¹ * a⁻¹) * a⁻¹) * (a * a) * (b * b) := by group
      rw [e1]
      exact V.mul_mem (V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTV haT) _).mp hc) iha.2) ihb.2
    | inv a _ iha =>
      refine ⟨Subgroup.inv_mem _ iha.1, ?_⟩
      have e1 : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      rw [e1]
      exact V.inv_mem iha.2
  exact key.2

theorem L_le_normalizer_yY : L ≤ Subgroup.normalizer ((yY L V H P : Subgroup G) : Set G) :=
  le_normalizer_conjClosure _ _

end Extra3

end Lem22

end CFSG.Quasithin.H13
