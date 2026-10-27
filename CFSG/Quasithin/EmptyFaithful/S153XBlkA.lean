module

public import CFSG.Quasithin.EmptyFaithful.S153XLoc
public import CFSG.Quasithin.EmptyFaithful.S153VRz
public import CFSG.Quasithin.EmptyFaithful.S153XBlkFin

public section

namespace CFSG.Quasithin.X1469.Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF CFSG.Quasithin.ModV
  CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

omit [Finite G] in
theorem pf_eq_toPerm {L : Subgroup G} (P : AppC.A5Pi L) {ℓ : G} (hℓ : ℓ ∈ L) :
    P.toPiData.pf ℓ = toPerm P.α ⟨ℓ, hℓ⟩ :=
  pf_eq_alpha P hℓ

omit [Finite G] in
theorem pf_comm {L : Subgroup G} (P : AppC.A5Pi L) {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    P.toPiData.pf (a * b * a⁻¹ * b⁻¹) =
      P.toPiData.pf a * P.toPiData.pf b * (P.toPiData.pf a)⁻¹ * (P.toPiData.pf b)⁻¹ := by
  have haN : a ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ha
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hb
  rw [P.toPiData.pf_mul (mul_mem (mul_mem haN hbN) (inv_mem haN)) (inv_mem hbN),
    P.toPiData.pf_mul (mul_mem haN hbN) (inv_mem haN), P.toPiData.pf_mul haN hbN,
    P.toPiData.pf_inv haN, P.toPiData.pf_inv hbN]

omit [Finite G] in
theorem card_eq_of_mem_iff {L : Subgroup G} (D : AppC.PiData L) {H : Subgroup G}
    (Q : evenWeight 5 → Prop) (hH : ∀ u, u ∈ H ↔ u ∈ blockU L ∧ Q (D.bf u)) :
    Nat.card H = Nat.card {w : evenWeight 5 // Q w} := by
  refine Nat.card_congr (Equiv.ofBijective (fun h => ⟨D.bf h, ((hH h).1 h.2).2⟩) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (D.bf_inj ((hH a).1 a.2).1 ((hH b).1 b.2).1 (congrArg Subtype.val hab))
  · intro w
    obtain ⟨u, hu, hbu⟩ := D.bf_surj w.1
    exact ⟨⟨u, (hH u).2 ⟨hu, hbu ▸ w.2⟩⟩, Subtype.ext hbu⟩

theorem card_subtype_even (Q : (Fin 5 → ZMod 2) → Prop) [DecidablePred Q] :
    Nat.card {w : evenWeight 5 // Q w.1} =
      (Finset.univ.filter fun f : Fin 5 → ZMod 2 => isEven f ∧ Q f).card := by
  rw [← Fintype.card_coe (Finset.univ.filter fun f : Fin 5 → ZMod 2 => isEven f ∧ Q f),
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun w => ⟨w.1.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w.1.2, w.2⟩⟩
      invFun := fun f => ⟨⟨f.1, by
        have := f.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this.1⟩, by
        have := f.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this.2⟩
      left_inv := fun w => rfl
      right_inv := fun f => rfl }

structure Ctx (I S Iz K₁ K₂ : Subgroup G) (P : AppC.A5Pi K₁) (p : Fin 5) : Prop where
  cfg : A5Cfg I S Iz K₁ K₂
  hnot : ¬ K₁ ≤ Iz
  hD : S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) = ⊥
  hp : ∀ g ∈ imgS K₁ S P.α, g p = p

namespace Ctx

variable {I S Iz K₁ K₂ : Subgroup G} {P : AppC.A5Pi K₁} {p : Fin 5} (X : Ctx I S Iz K₁ K₂ P p)
include X

theorem mem_S_iff {ℓ : G} (hℓ : ℓ ∈ K₁) : ℓ ∈ S ↔ P.toPiData.pf ℓ ∈ klein p := by
  rw [pf_eq_toPerm P hℓ]
  exact X.cfg.memS_iff P X.hp ⟨ℓ, hℓ⟩

theorem mem_Iz_iff {ℓ : G} (hℓ : ℓ ∈ K₁) : ℓ ∈ Iz ↔ P.toPiData.pf ℓ p = p := by
  constructor
  · intro h
    rw [pf_eq_toPerm P hℓ]
    exact X.cfg.inf_Iz_fix P X.hp X.hnot ⟨ℓ, hℓ⟩ h
  · intro h
    exact X.cfg.lift_mem_Iz P X.hp h ⟨ℓ, hℓ⟩ (pf_eq_toPerm P hℓ).symm

theorem exists_lift_Y {σ : Perm (Fin 5)} (hσ : Perm.sign σ = 1) (hσp : σ p = p) :
    ∃ y ∈ K₁ ⊓ Iz, P.toPiData.pf y = σ := by
  obtain ⟨x, hx⟩ := A5Cfg.exists_lift P σ hσ
  exact ⟨x, ⟨x.2, X.cfg.lift_mem_Iz P X.hp hσp x hx⟩, by rw [pf_eq_toPerm P x.2]; exact hx⟩

theorem exists_lift_B {v : Perm (Fin 5)} (hv : v ∈ klein p) :
    ∃ b ∈ S ⊓ K₁, P.toPiData.pf b = v :=
  X.cfg.exists_mem_inf_pf_eq P X.hp hv

theorem mem_U_of_pf {x : G} (hx : x ∈ K₁) (h : P.toPiData.pf x = 1) : x ∈ blockU K₁ := by
  have hα : P.α ⟨x, hx⟩ = 1 := Subtype.ext (by rw [← pf_eq_alpha P hx]; exact h)
  have hQ : x ∈ blockQ K₁ := (AppC.mem_pCore_iff_mem_blockQ _).mp (by rw [← P.hαk]; exact hα)
  obtain ⟨u, hu, d, hd, rfl⟩ := X.cfg.exists_U_mul_D hQ
  have hd' : d ∈ (⊥ : Subgroup G) := by
    rw [← X.hD]
    exact hd
  rw [Subgroup.mem_bot.mp hd', mul_one]
  exact hu

omit [Finite G] in
theorem pf_U {u : G} (hu : u ∈ blockU K₁) : P.toPiData.pf u = 1 :=
  pf_eq_one_of_mem_blockQ P (C1.blockU_le_blockQ X.cfg.blk₁.1 hu)

theorem mem_Z_iff {u : G} : u ∈ Zsub S K₁ ↔
    u ∈ blockU K₁ ∧ ((P.toPiData.bf u).1 = 0 ∨ (P.toPiData.bf u).1 = zvec p) := by
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, fix_klein p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf u).2) fun v hv => ?_⟩
    obtain ⟨b, hb, hpfb⟩ := X.exists_lift_B hv
    have h1 := (P.toPiData.comm_iff (Subgroup.le_normalizer hb.2) hu).mp
      (Subgroup.mem_centralizer_iff.mp hc b hb)
    rw [hpfb] at h1
    exact congrArg Subtype.val h1
  · rintro ⟨hu, h⟩
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hv : P.toPiData.pf b ∈ klein p := (X.mem_S_iff hb.2).mp hb.1
    refine (P.toPiData.comm_iff (Subgroup.le_normalizer hb.2) hu).mpr (Subtype.ext ?_)
    show pact (P.toPiData.pf b) (P.toPiData.bf u).1 = (P.toPiData.bf u).1
    rcases h with h | h <;> rw [h]
    · rfl
    · exact pact_zvec p _ (fix_of_klein hv)

theorem mem_E_iff {e : G} : e ∈ Esub K₁ Iz ↔ e ∈ blockU K₁ ∧ (P.toPiData.bf e).1 p = 0 := by
  constructor
  · intro he
    let E' : Subgroup G :=
      { carrier := {u | u ∈ blockU K₁ ∧ (P.toPiData.bf u).1 p = 0}
        one_mem' := ⟨one_mem _, by rw [P.toPiData.bf_one]; rfl⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          rw [P.toPiData.bf_mul ha.1 hb.1]
          show (P.toPiData.bf a).1 p + (P.toPiData.bf b).1 p = 0
          rw [ha.2, hb.2, add_zero]⟩
        inv_mem' := fun {a} ha => by
          have h2 : a⁻¹ = a :=
            inv_eq_of_mul_eq_one_right (by rw [← sq]; exact C1.blockU_sq X.cfg.blk₁.1 a ha.1)
          rw [h2]
          exact ha }
    have hle : Esub K₁ Iz ≤ E' := by
      rw [Esub, Subgroup.commutator_le]
      intro u hu y hy
      rw [commutatorElement_def]
      refine ⟨A5Cfg.comm_mem_U hu hy.1, ?_⟩
      rw [X.cfg.bf_comm P hu hy.1]
      have hfix : (P.toPiData.pf y)⁻¹ p = p := by
        rw [Perm.inv_eq_iff_eq]
        exact ((X.mem_Iz_iff hy.1).mp hy.2).symm
      show (P.toPiData.bf u).1 p + (P.toPiData.bf u).1 ((P.toPiData.pf y)⁻¹ p) = 0
      rw [hfix]
      exact zmod_two_add_self _
    exact hle he
  · rintro ⟨hu, h0⟩
    obtain ⟨σ, hσs, hσp, w, hw, hx⟩ :=
      exists_comm_rep p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf e).2) h0
    obtain ⟨u', hu', hbu'⟩ := P.toPiData.bf_surj ⟨w, (mem_evenWeight_iff _).mpr hw⟩
    obtain ⟨y, hy, hpfy⟩ := X.exists_lift_Y hσs hσp
    have hc : u' * y * u'⁻¹ * y⁻¹ = e := by
      apply P.toPiData.bf_inj (A5Cfg.comm_mem_U hu' hy.1) hu
      apply Subtype.ext
      rw [X.cfg.bf_comm P hu' hy.1, hbu', hpfy]
      exact hx.symm
    rw [← hc, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hu' hy

theorem card_E : Nat.card ↥(Esub K₁ Iz) = 8 := by
  rw [card_eq_of_mem_iff P.toPiData (fun w => w.1 p = 0) fun e => X.mem_E_iff,
    card_subtype_even (fun f => f p = 0)]
  exact card_vanish p

theorem card_Z : Nat.card ↥(Zsub S K₁) = 2 := by
  rw [card_eq_of_mem_iff P.toPiData (fun w => w.1 = 0 ∨ w.1 = zvec p) fun e => X.mem_Z_iff,
    card_subtype_even (fun f => f = 0 ∨ f = zvec p)]
  exact card_line p

theorem Z_le_E : Zsub S K₁ ≤ Esub K₁ Iz := by
  intro u hu
  obtain ⟨huU, h⟩ := X.mem_Z_iff.mp hu
  refine X.mem_E_iff.mpr ⟨huU, ?_⟩
  rcases h with h | h <;> rw [h]
  · rfl
  · exact zvec_self p

theorem faith_E : ∀ b ∈ S ⊓ K₁, (∀ e ∈ Esub K₁ Iz, b * e * b⁻¹ = e) → b ∈ blockU K₁ := by
  intro b hb h
  have hv : P.toPiData.pf b ∈ klein p := (X.mem_S_iff hb.2).mp hb.1
  have hbN : b ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hb.2
  refine X.mem_U_of_pf hb.2 (klein_faithful p _ hv fun x hx hxp => ?_)
  obtain ⟨e, he, hbe⟩ := P.toPiData.bf_surj ⟨x, (mem_evenWeight_iff _).mpr hx⟩
  have heE : e ∈ Esub K₁ Iz := X.mem_E_iff.mpr ⟨he, by rw [hbe]; exact hxp⟩
  have h1 := P.toPiData.bf_conj hbN he
  rw [h e heE, hbe] at h1
  exact (congrArg Subtype.val h1).symm

theorem Y_le_N_B : K₁ ⊓ Iz ≤ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) :=
  fun y hy => X.cfg.inf_Iz_le_normalizer P X.hp X.hnot y hy.1 hy.2

end Ctx

end CFSG.Quasithin.X1469.Blk
