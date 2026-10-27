module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Swp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Mod
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Ball

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem beta_surj (F : FanTree Γ G) (h : Fan71c F L) : ∀ w, Γ.Adj α w → ∃ i, D.beta i = w := by
  have hα' : Nat.card (Γ.neighborSet α) = 5 := D.val
  have hfin : Finite (Γ.neighborSet α) := Nat.finite_of_card_ne_zero (by omega)
  let f : Fin 5 → Γ.neighborSet α := fun i => ⟨D.beta i, D.adj_start_beta i⟩
  have hf : Function.Injective f := fun i j e => D.beta_injective F h (congrArg Subtype.val e)
  have hb := hf.bijective_of_nat_card_le (by rw [hα']; simp)
  intro w hw
  obtain ⟨i, hi⟩ := hb.2 ⟨w, hw⟩
  exact ⟨i, congrArg Subtype.val hi⟩

@[expose] noncomputable def sig (g : G) : Fin 5 → ZMod 2 := fun i => swp Γ G g (D.beta i)

@[expose] def SigSet (v : Fin 5 → ZMod 2) : Prop := ∃ g ∈ nbrStab Γ G α, sig D g = v

theorem sig_one : sig D 1 = 0 := by
  funext i
  exact swp_eq_zero_iff.2 (Subgroup.one_mem _)

theorem sig_mul (F : FanTree Γ G) {g h : G} (hg : g ∈ nbrStab Γ G α) (hh : h ∈ nbrStab Γ G α) :
    sig D (g * h) = sig D g + sig D h := by
  funext i
  exact swp_mul F D.val (D.adj_start_beta i) hg hh

theorem sig_conj (F : FanTree Γ G) (h : Fan71c F L) (g : G) :
    sig D (D.x⁻¹ * g * D.x) = sh (sig D g) := by
  funext i
  have hx : D.x • D.beta i = D.beta (i - 1) := by
    have h1 := D.x_inv_smul_vert F h (i - 1) (m := 1) (by norm_num)
    rw [sub_add_cancel] at h1
    have h2 : D.x⁻¹ • D.beta (i - 1) = D.beta i := h1
    rw [← h2, smul_inv_smul]
  show swp Γ G (D.x⁻¹ * g * D.x) (D.beta i) = swp Γ G g (D.beta (i - 1))
  rw [← swp_smul F D.x g (D.beta i), hx]

theorem sig_eq_zero_iff (F : FanTree Γ G) (h : Fan71c F L) {g : G} (hg : g ∈ nbrStab Γ G α) :
    sig D g = 0 ↔ g ∈ ballStab Γ G 2 α := by
  rw [F.mem_ballStab_two_iff]
  constructor
  · intro h0
    refine ⟨hg, fun γ hγ => ?_⟩
    obtain ⟨i, rfl⟩ := beta_surj D F h γ hγ
    exact swp_eq_zero_iff.1 (congrFun h0 i)
  · rintro ⟨-, h2⟩
    funext i
    exact swp_eq_zero_iff.2 (h2 _ (D.adj_start_beta i))

theorem SigSet_zero : SigSet D 0 := ⟨1, Subgroup.one_mem _, sig_one D⟩

theorem SigSet_add (F : FanTree Γ G) {a b : Fin 5 → ZMod 2} (ha : SigSet D a) (hb : SigSet D b) :
    SigSet D (a + b) := by
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨k, hk, rfl⟩ := hb
  exact ⟨g * k, Subgroup.mul_mem _ hg hk, sig_mul D F hg hk⟩

theorem SigSet_sh (F : FanTree Γ G) (h : Fan71c F L) {a : Fin 5 → ZMod 2} (ha : SigSet D a) :
    SigSet D (sh a) := by
  obtain ⟨g, hg, rfl⟩ := ha
  have hx : D.x⁻¹ ∈ MulAction.stabilizer G α := inv_mem (D.x_mem_stabilizer F h)
  refine ⟨D.x⁻¹ * g * D.x, ?_, sig_conj D F h g⟩
  have := F.conj_mem_nbrStab_of_stab hx hg
  simpa using this

@[expose] noncomputable def sigHom (F : FanTree Γ G) :
    ↥(nbrStab Γ G α) →* Multiplicative (Fin 5 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (sig D g)
  map_one' := by
    show Multiplicative.ofAdd (sig D 1) = 1
    rw [sig_one D]
    rfl
  map_mul' g k := by
    show Multiplicative.ofAdd (sig D (g * k)) =
      Multiplicative.ofAdd (sig D g) * Multiplicative.ofAdd (sig D k)
    rw [sig_mul D F g.2 k.2]
    rfl

theorem sigHom_ker (F : FanTree Γ G) (h : Fan71c F L) :
    (sigHom D F).ker = (ballStab Γ G 2 α).subgroupOf (nbrStab Γ G α) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← sig_eq_zero_iff D F h g.2]
  show Multiplicative.ofAdd (sig D g) = 1 ↔ sig D g = 0
  exact ⟨fun e => e, fun e => e⟩

theorem relIndex_eq_range (F : FanTree Γ G) (h : Fan71c F L) :
    (ballStab Γ G 2 α).relIndex (nbrStab Γ G α) = Nat.card (sigHom D F).range := by
  rw [← Subgroup.index_ker, sigHom_ker D F h]
  rfl

theorem relIndex_eq_card (F : FanTree Γ G) (h : Fan71c F L) [DecidablePred (SigSet D)] :
    (ballStab Γ G 2 α).relIndex (nbrStab Γ G α) = (Finset.univ.filter (SigSet D)).card := by
  rw [relIndex_eq_range D F h]
  have e : (sigHom D F).range ≃ {v : Fin 5 → ZMod 2 // SigSet D v} :=
    { toFun := fun y => ⟨Multiplicative.toAdd y.1, by
        obtain ⟨g, hg⟩ := y.2
        exact ⟨g, g.2, by rw [← hg]; rfl⟩⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, by
        obtain ⟨g, hg, hv⟩ := v.2
        exact ⟨⟨g, hg⟩, by
          show Multiplicative.ofAdd (sig D g) = Multiplicative.ofAdd v.1
          rw [hv]⟩⟩
      left_inv := fun y => by simp
      right_inv := fun v => by simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

end P73

end CFSG.Quasithin.Fan86
