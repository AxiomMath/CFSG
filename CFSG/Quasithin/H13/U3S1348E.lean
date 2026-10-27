module

public import CFSG.Quasithin.H13.U3S1348D
public import CFSG.Quasithin.H13.U3S1348K
public import CFSG.Quasithin.H13.U3S13227P
public import CFSG.Quasithin.H13.NQS1342

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def InW3s (x : P6) : Prop :=
  Multiplicative.toAdd x 4 = 0 ∧ Multiplicative.toAdd x 5 = 0

instance : DecidablePred InW3s := fun x => by unfold InW3s; infer_instance

@[expose] def W3s : Subgroup ↥(G6.coreMod 6) where
  carrier := {y | InW3s (y : P6)}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : P6, InW3s a → InW3s b → InW3s (a * b) := by decide +kernel
    exact key _ _ ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : P6, InW3s a → InW3s a⁻¹ := by decide +kernel
    exact key _ ha)

@[expose] def W3list : List P6 :=
  [1, pv 0 1, pv 0 2, pv 0 3, pv 1 2, pv 1 3, pv 2 3, e0123]

theorem w3_mem_list : ∀ y : P6, y ∈ G6.coreMod 6 → InW3s y → y ∈ W3list := by decide +kernel

theorem w3_list_mem : ∀ y ∈ W3list, y ∈ G6.coreMod 6 ∧ InW3s y := by decide +kernel

theorem w3_gen : ∀ y ∈ W3list, ∃ a ∈ W3list, ∃ b ∈ W3list,
    y = a * (G6.permAct 6 c012 a)⁻¹ * (b * (G6.permAct 6 c123 b)⁻¹) := by
  decide +kernel

theorem w3_fix : ∀ σ ∈ K4xList, (∀ a ∈ W3list, G6.permAct 6 σ a = a) →
    ∀ x : P6, x ∈ G6.coreMod 6 →
      x * (G6.permAct 6 σ x)⁻¹ = 1 ∨ x * (G6.permAct 6 σ x)⁻¹ = e45 := by
  decide +kernel

theorem quad_K4 : ∀ κ ∈ K4List, ∀ κ' ∈ K4List, κ ≠ 1 → κ' ≠ 1 → κ ≠ κ' →
    ∃ x : P6, x ∈ G6.coreMod 6 ∧
      G6.permAct 6 κ' (x * (G6.permAct 6 κ x)⁻¹) ≠ x * (G6.permAct 6 κ x)⁻¹ := by
  decide +kernel

theorem c012_conj_K4 : ∀ κ ∈ K4List, κ ≠ 1 →
    c012 * κ * c012⁻¹ ∈ K4List ∧ c012 * κ * c012⁻¹ ≠ 1 ∧ c012 * κ * c012⁻¹ ≠ κ := by
  decide +kernel

theorem allOnes_eq_mul : G6.allOnes 6 = e0123 * e45 := by decide

theorem e0123_mem_W3list : e0123 ∈ W3list := by decide

theorem inW3s_permAct {σ : Perm (Fin 6)} (h4 : σ 4 = 4) (h5 : σ 5 = 5) {x : P6}
    (hx : InW3s x) : InW3s (G6.permAct 6 σ x) := by
  have h4' : σ⁻¹ 4 = 4 := by rw [Perm.inv_eq_iff_eq, h4]
  have h5' : σ⁻¹ 5 = 5 := by rw [Perm.inv_eq_iff_eq, h5]
  exact ⟨by rw [G6.permAct_apply, h4']; exact hx.1, by rw [G6.permAct_apply, h5']; exact hx.2⟩

theorem inW3s_comm {σ : Perm (Fin 6)} (h4 : σ 4 = 4) (h5 : σ 5 = 5) (x : P6) :
    InW3s (x * (G6.permAct 6 σ x)⁻¹) := by
  have h4' : σ⁻¹ 4 = 4 := by rw [Perm.inv_eq_iff_eq, h4]
  have h5' : σ⁻¹ 5 = 5 := by rw [Perm.inv_eq_iff_eq, h5]
  refine ⟨?_, ?_⟩
  · rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply, h4']
    exact add_neg_cancel _
  · rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply, h5']
    exact add_neg_cancel _

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem map_conj_le_of_mem_normalizer {X K : Subgroup G} {g : G} (hXK : X ≤ K)
    (hg : g ∈ normalizer (K : Set G)) : X.map (MulAut.conj g).toMonoidHom ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  exact (mem_normalizer_iff.mp hg y).mp (hXK hy)

theorem s134_comm_V (S : A6.Setting134 G T L V) {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a := by
  have h := congrArg Subtype.val ((s134_elemAbelian_V S).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  simpa using h

theorem s134_comm_V_conj (S : A6.Setting134 G T L V) {g a b : G}
    (ha : a ∈ V.map (MulAut.conj g).toMonoidHom) (hb : b ∈ V.map (MulAut.conj g).toMonoidHom) :
    a * b = b * a := by
  have h := s134_comm_V S (mem_map_conj_iff.1 ha) (mem_map_conj_iff.1 hb)
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

@[expose] noncomputable def s134V3 (S : A6.Setting134 G T L V) : Subgroup G := S.pre W3s

theorem mem_s134V3 (S : A6.Setting134 G T L V) {x : G} :
    x ∈ s134V3 S ↔ ∃ h : x ∈ V, InW3s (S.frame.ψ ⟨x, h⟩ : P6) := S.mem_pre

theorem s134V3_le_V (S : A6.Setting134 G T L V) : s134V3 S ≤ V := fun _ hx =>
  ((mem_s134V3 S).1 hx).1

theorem s134_pre_mem (S : A6.Setting134 G T L V) {y : P6} (hy : y ∈ G6.coreMod 6)
    (hW : InW3s y) : (S.frame.ψ.symm ⟨y, hy⟩ : G) ∈ s134V3 S :=
  (mem_s134V3 S).2 ⟨(S.frame.ψ.symm ⟨y, hy⟩).2, by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact hW⟩

theorem s134_commutator_le_V3 (S : A6.Setting134 G T L V) :
    ⁅V, L₁Of L (fsuV1 T V)⁆ ≤ s134V3 S := by
  rw [commutator_le]
  intro v hv l hl
  have hlN : l ∈ normalizer (V : Set G) := S.frame.L_le (L1Of_le L _ hl)
  obtain ⟨hmem, hψ⟩ := s134_psi_comm S hlN hv
  refine (mem_s134V3 S).2 ⟨hmem, ?_⟩
  obtain ⟨h4, h5, -⟩ := s134_rho_L1 S hlN hl
  rw [hψ]
  exact inW3s_comm h4 h5 _

theorem s134_L1_le_normalizer_V3 (S : A6.Setting134 G T L V) :
    L₁Of L (fsuV1 T V) ≤ normalizer (s134V3 S : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun l hl w hw => ?_
  obtain ⟨hwV, hwW⟩ := (mem_s134V3 S).1 hw
  have hlN : l ∈ normalizer (V : Set G) := S.frame.L_le (L1Of_le L _ hl)
  refine (mem_s134V3 S).2 ⟨(mem_normalizer_iff.mp hlN w).mp hwV, ?_⟩
  rw [S.psi_conj ⟨l, hlN⟩ ⟨w, hwV⟩, G6.coreAct_coe]
  obtain ⟨h4, h5, -⟩ := s134_rho_L1 S hlN hl
  exact inW3s_permAct h4 h5 hwW

theorem s134_V3_le_commutator (S : A6.Setting134 G T L V) :
    s134V3 S ≤ ⁅s134V3 S, L₁Of L (fsuV1 T V)⁆ := by
  intro w hw
  obtain ⟨hwV, hwW⟩ := (mem_s134V3 S).1 hw
  obtain ⟨a, ha, b, hb, hab⟩ := w3_gen _ (w3_mem_list _ (S.frame.ψ ⟨w, hwV⟩).2 hwW)
  obtain ⟨x₁, hx₁L, hx₁N, hx₁⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  obtain ⟨x₂, hx₂L, hx₂N, hx₂⟩ := s134_exists_mem_L1 S c123_props.1 c123_props.2.1
    c123_props.2.2
  obtain ⟨haC, haW⟩ := w3_list_mem a ha
  obtain ⟨hbC, hbW⟩ := w3_list_mem b hb
  have hvaV3 := s134_pre_mem S haC haW
  have hvbV3 := s134_pre_mem S hbC hbW
  obtain ⟨hc₁, h1⟩ := s134_psi_comm S hx₁N (S.frame.ψ.symm ⟨a, haC⟩).2
  obtain ⟨hc₂, h2⟩ := s134_psi_comm S hx₂N (S.frame.ψ.symm ⟨b, hbC⟩).2
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, hx₁] at h1
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, hx₂] at h2
  have key : (⟨w, hwV⟩ : ↥V) = ⟨_, hc₁⟩ * ⟨_, hc₂⟩ := by
    apply S.frame.ψ.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, h1, h2]
    exact hab
  have heq := congrArg Subtype.val key
  simp only [Subgroup.coe_mul] at heq
  rw [heq]
  exact mul_mem (commutator_mem_commutator hvaV3 hx₁L) (commutator_mem_commutator hvbV3 hx₂L)

theorem s134_exists_conj_not_le (S : A6.Setting134 G T L V) (hL : IsShort2 L) {H : Subgroup G}
    (hTH : T ≤ H) (hHM : ¬ H ≤ normalizer (L : Set G)) (hVO : V ≤ pCoreOf 2 H)
    (hOT : pCoreOf 2 H ≤ T) :
    ∃ h ∈ H, ¬ V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  set U := conjClosure V H with hUdef
  have hUC : U ≤ centralizer (V : Set G) :=
    conjClosure_le fun h hh v hv => hall h hh (conj_mem_map_conj hv)
  have hUO : U ≤ pCoreOf 2 H := conjClosure_le fun h hh v hv =>
    (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) v).mp (hVO hv)
  have hUQ : U ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← s134_cT S]
    exact le_inf (hUO.trans hOT) hUC
  have hVU : V ≤ U := le_conjClosure V H
  have hLU : L ≤ normalizer (U : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun l hl u hu => ?_
    have h1 := s134_commutator_mem_V S hL (hUQ (U.inv_mem hu)) hl
    have e : l * u * l⁻¹ = u * (u⁻¹ * l * u⁻¹⁻¹ * l⁻¹) := by group
    rw [e]
    exact U.mul_mem hu (hVU h1)
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjClosure V H
  have hU1 : U ≠ ⊥ := fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ hVU))
  have hU2 : IsPGroup 2 ↥U := S.h13.sylow.1.to_le (hUO.trans hOT)
  exact hHM (hHU.trans (s134_normalizer_le_M S hU1 hU2 (sup_le hLU (hTH.trans hHU))))

theorem s134_V3conj_le (S : A6.Setting134 G T L V) {H : Subgroup G}
    (hHL1 : H ≤ normalizer (L₁Of L (fsuV1 T V) : Set G)) (hL1H : L₁Of L (fsuV1 T V) ≤ H)
    (hVO : V ≤ pCoreOf 2 H) {g : G} (hg : g ∈ H) :
    (s134V3 S).map (MulAut.conj g).toMonoidHom ≤
        ⁅(s134V3 S).map (MulAut.conj g).toMonoidHom, L₁Of L (fsuV1 T V)⁆ ∧
      (s134V3 S).map (MulAut.conj g).toMonoidHom ≤ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set W := (s134V3 S).map (MulAut.conj g).toMonoidHom with hW
  have h1 : W ≤ ⁅W, L₁⁆ := by
    have h := map_mono (f := (MulAut.conj g).toMonoidHom) (s134_V3_le_commutator S)
    rwa [map_commutator, GammaExtra.map_conj_eq_self_of_mem_normalizer (hHL1 hg)] at h
  refine ⟨h1, h1.trans ?_⟩
  have hWO : W ≤ pCoreOf 2 H :=
    map_conj_le_of_mem_normalizer ((s134V3_le_V S).trans hVO) (le_normalizer_pCoreOf 2 H hg)
  have hc : ⁅pCoreOf 2 H, L₁⁆ ≤ pCoreOf 2 H ⊓ L₁ := by
    rw [commutator_le]
    intro o ho l hl
    rw [commutatorElement_def]
    have h2 : l * o⁻¹ * l⁻¹ ∈ pCoreOf 2 H :=
      (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hL1H hl)) _).mp
        ((pCoreOf 2 H).inv_mem ho)
    have h3 : o * l * o⁻¹ ∈ L₁ := (mem_normalizer_iff.mp (hHL1 (pCoreOf_le 2 H ho)) l).mp hl
    have e : o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) := by group
    refine mem_inf.2 ⟨?_, L₁.mul_mem h3 (L₁.inv_mem hl)⟩
    rw [e]
    exact (pCoreOf 2 H).mul_mem ho h2
  have hO : pCoreOf 2 H ⊓ L₁ ≤ pCoreOf 2 L₁ := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun l hl => ?_)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    exact mem_normalizer_inf_of (le_normalizer_pCoreOf 2 H (hL1H hl)) (le_normalizer hl)
  exact (commutator_mono hWO le_rfl).trans (hc.trans hO)

theorem s134_L1_le_normalizer_V3conj (S : A6.Setting134 G T L V) {g : G}
    (hg : g ∈ normalizer (L₁Of L (fsuV1 T V) : Set G)) :
    L₁Of L (fsuV1 T V) ≤
      normalizer (((s134V3 S).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun l hl w hw => ?_
  have hw' := mem_map_conj_iff.1 hw
  have hl' : g⁻¹ * l * g ∈ L₁Of L (fsuV1 T V) := by
    have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
    simpa using this
  have h1 := (mem_normalizer_iff.mp (s134_L1_le_normalizer_V3 S hl') _).mp hw'
  refine mem_map_conj_iff.2 ?_
  have e : g⁻¹ * (l * w * l⁻¹) * g =
      (g⁻¹ * l * g) * (g⁻¹ * w * g) * (g⁻¹ * l * g)⁻¹ := by group
  rw [e]
  exact h1

theorem s134_V3conj_le_centralizer (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H : Subgroup G}
    (hHL1 : H ≤ normalizer (L₁Of L (fsuV1 T V) : Set G)) (hL1H : L₁Of L (fsuV1 T V) ≤ H)
    (hVO : V ≤ pCoreOf 2 H) (hON : pCoreOf 2 H ≤ normalizer (V : Set G)) {g : G} (hg : g ∈ H) :
    (s134V3 S).map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set W := (s134V3 S).map (MulAut.conj g).toMonoidHom with hW
  have P := s134Plus_L1 S he
  obtain ⟨-, hWO⟩ := s134_V3conj_le S hHL1 hL1H hVO hg
  have hWVg : W ≤ V.map (MulAut.conj g).toMonoidHom := map_mono (s134V3_le_V S)
  have hK : ∀ a ∈ W, ∀ ha : a ∈ normalizer (V : Set G), S.frame.ρ ⟨a, ha⟩ ∈ K4List := by
    intro a haW ha
    have haO := hWO haW
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L₁ ⟨a, haO⟩
    have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : S.frame.ρ ⟨a, ha⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    exact A4_two_K4 _ (s134_rho_L1 S ha (pCoreOf_le 2 L₁ haO)) (pow_sixteen_of_two_pow h1)
  have hWN : ∀ a ∈ W, a ∈ normalizer (V : Set G) := fun a haW =>
    S.frame.T_le (P.pCoreOf_le_T (hWO haW))
  have hVN : ∀ v ∈ V, ∀ b ∈ V.map (MulAut.conj g).toMonoidHom,
      v * b * v⁻¹ ∈ V.map (MulAut.conj g).toMonoidHom := by
    intro v hv b hb
    have hv' : g⁻¹ * v * g ∈ pCoreOf 2 H := by
      have := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (inv_mem hg)) v).mp (hVO hv)
      simpa using this
    have h1 := (mem_normalizer_iff.mp (hON hv') _).mp (mem_map_conj_iff.1 hb)
    refine mem_map_conj_iff.2 ?_
    have e : g⁻¹ * (v * b * v⁻¹) * g =
        (g⁻¹ * v * g) * (g⁻¹ * b * g) * (g⁻¹ * v * g)⁻¹ := by group
    rw [e]
    exact h1
  intro a haW
  by_contra haC
  have ha := hWN a haW
  have hρ1 : S.frame.ρ ⟨a, ha⟩ ≠ 1 := fun h => haC ((s134_rho_eq_one_iff S _).1 h)
  obtain ⟨c, hcL, hcN, hc⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1 c012_props.2.2
  have ha'W : c * a * c⁻¹ ∈ W := (mem_normalizer_iff.mp
    (s134_L1_le_normalizer_V3conj S (hHL1 hg) hcL) a).mp haW
  have ha' := hWN _ ha'W
  have hρa' : S.frame.ρ ⟨c * a * c⁻¹, ha'⟩ = c012 * S.frame.ρ ⟨a, ha⟩ * c012⁻¹ := by
    rw [show (⟨c * a * c⁻¹, ha'⟩ : ↥(normalizer (V : Set G))) =
      ⟨c, hcN⟩ * ⟨a, ha⟩ * ⟨c, hcN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, hc]
  obtain ⟨hK', hne1, hne⟩ := c012_conj_K4 _ (hK a haW ha) hρ1
  obtain ⟨x, hxC, hx⟩ := quad_K4 _ (hK a haW ha) _ hK' hρ1 hne1 hne.symm
  obtain ⟨v, hv, hψv⟩ : ∃ v : G, ∃ hv : v ∈ V, S.frame.ψ ⟨v, hv⟩ = ⟨x, hxC⟩ :=
    ⟨_, (S.frame.ψ.symm ⟨x, hxC⟩).2, by rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]⟩
  obtain ⟨hwV, hψw⟩ := s134_psi_comm S ha hv
  rw [hψv] at hψw
  have hwVg : ⁅v, a⁆ ∈ V.map (MulAut.conj g).toMonoidHom := by
    rw [commutatorElement_def]
    exact mul_mem (hVN v hv a (hWVg haW)) (inv_mem (hWVg haW))
  have hcomm := s134_comm_V_conj S (hWVg ha'W) hwVg
  have hfix : (c * a * c⁻¹) * ⁅v, a⁆ * (c * a * c⁻¹)⁻¹ = ⁅v, a⁆ := by
    rw [hcomm]
    group
  have h1 := (S.conj_eq_iff ⟨c * a * c⁻¹, ha'⟩ ⟨_, hwV⟩).1 hfix
  have h2 := congrArg Subtype.val h1
  rw [G6.coreAct_coe, hρa', hψw] at h2
  exact hx h2

theorem s134_V3conj_eq (S : A6.Setting134 G T L V) (hL : IsShort2 L)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H : Subgroup G}
    (hHL1 : H ≤ normalizer (L₁Of L (fsuV1 T V) : Set G)) (hL1H : L₁Of L (fsuV1 T V) ≤ H)
    (hVO : V ≤ pCoreOf 2 H) {g : G} (hg : g ∈ H)
    (hWC : (s134V3 S).map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    (s134V3 S).map (MulAut.conj g).toMonoidHom = s134V3 S := by
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set W := (s134V3 S).map (MulAut.conj g).toMonoidHom with hW
  obtain ⟨h1, hWO⟩ := s134_V3conj_le S hHL1 hL1H hVO hg
  have hWL : W ≤ L := hWO.trans ((pCoreOf_le 2 L₁).trans (L1Of_le L _))
  have hWQ : W ≤ pCoreOf 2 L := by
    rw [s134_pCoreOf_L_eq S he]
    exact le_inf hWL hWC
  have hWV : W ≤ V := by
    refine h1.trans ?_
    have h2 : ⁅W, L₁⁆ ≤ blockU L := commutator_mono hWQ (L1Of_le L _)
    rwa [s134_blockU_eq_V S hL] at h2
  have hle : W ≤ s134V3 S := h1.trans ((commutator_mono hWV le_rfl).trans
    (s134_commutator_le_V3 S))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hW, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem s134_false_of_normal (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (S : A6.Setting134 G T L V)
    (hL : IsShort2 L) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    {H : Subgroup G} (hHL1 : H ≤ normalizer (L₁Of L (fsuV1 T V) : Set G))
    (hL1H : L₁Of L (fsuV1 T V) ≤ H) (hVO : V ≤ pCoreOf 2 H) (hOR : pCoreOf 2 H ≤ r1Of T L V)
    {h : G} (hh : h ∈ H) (hnot : ¬ V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hON : pCoreOf 2 H ≤ normalizer (V : Set G) :=
    hOR.trans ((r1Of_le_T T L V).trans S.frame.T_le)
  set Vh := V.map (MulAut.conj h).toMonoidHom with hVh
  have hWC := s134_V3conj_le_centralizer S he hHL1 hL1H hVO hON hh
  have hWeq := s134_V3conj_eq S hL he hHL1 hL1H hVO hh hWC
  have hV3Vh : s134V3 S ≤ Vh := hWeq ▸ map_mono (s134V3_le_V S)
  have hVhO : Vh ≤ pCoreOf 2 H := map_conj_le_of_mem_normalizer hVO (le_normalizer_pCoreOf 2 H hh)
  have hVN : ∀ v ∈ V, ∀ b ∈ Vh, v * b * v⁻¹ ∈ Vh := by
    intro v hv b hb
    have hv' : h⁻¹ * v * h ∈ pCoreOf 2 H := by
      have := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (inv_mem hh)) v).mp (hVO hv)
      simpa using this
    have h1 := (mem_normalizer_iff.mp (hON hv') _).mp (mem_map_conj_iff.1 hb)
    refine mem_map_conj_iff.2 ?_
    have e : h⁻¹ * (v * b * v⁻¹) * h =
        (h⁻¹ * v * h) * (h⁻¹ * b * h) * (h⁻¹ * v * h)⁻¹ := by group
    rw [e]
    exact h1
  obtain ⟨a, haVh, haC⟩ := Set.not_subset.1 hnot
  have haN : a ∈ normalizer (V : Set G) := hON (hVhO haVh)
  obtain ⟨v, hv, hva⟩ : ∃ v ∈ V, v * a ≠ a * v := by
    by_contra hall
    push Not at hall
    exact haC (mem_centralizer_iff.2 fun v hv => hall v hv)
  have haK : S.frame.ρ ⟨a, haN⟩ ∈ K4xList :=
    ((s134_mem_r1Of_iff S).1 (hOR (hVhO haVh))).2 haN
  have hfixW : ∀ y ∈ W3list, G6.permAct 6 (S.frame.ρ ⟨a, haN⟩) y = y := by
    intro y hy
    obtain ⟨hyC, hyW⟩ := w3_list_mem y hy
    have hw := s134_pre_mem S hyC hyW
    have hcomm := s134_comm_V_conj S haVh (hV3Vh hw)
    have hfix : a * (S.frame.ψ.symm ⟨y, hyC⟩ : G) * a⁻¹ = S.frame.ψ.symm ⟨y, hyC⟩ := by
      rw [hcomm]
      group
    have h1 := (S.conj_eq_iff ⟨a, haN⟩ (S.frame.ψ.symm ⟨y, hyC⟩)).1 hfix
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val h1
    rwa [G6.coreAct_coe] at h2
  obtain ⟨hwV, hψw⟩ := s134_psi_comm S haN hv
  have hwVh : ⁅v, a⁆ ∈ Vh := by
    rw [commutatorElement_def]
    exact mul_mem (hVN v hv a haVh) (inv_mem haVh)
  have hwe : (S.frame.ψ ⟨⁅v, a⁆, hwV⟩ : P6) = e45 := by
    rw [hψw]
    rcases w3_fix _ haK hfixW _ (S.frame.ψ ⟨v, hv⟩).2 with h0 | h0
    · exfalso
      apply hva
      have h1 : S.frame.ψ ⟨⁅v, a⁆, hwV⟩ = 1 := by
        apply Subtype.ext
        rw [hψw]
        exact h0
      have h2 := congrArg Subtype.val (S.frame.ψ.map_eq_one_iff.1 h1)
      simp only [Subgroup.coe_one] at h2
      calc v * a = ⁅v, a⁆ * (a * v) := by rw [commutatorElement_def]; group
        _ = a * v := by rw [h2, one_mul]
    · exact h0
  have hzV : S.zV ∈ Vh := by
    have h0 := s134_pre_mem S e0123_mem (w3_list_mem _ e0123_mem_W3list).2
    have key : (⟨S.zV, S.zV_mem_V⟩ : ↥V) =
        S.frame.ψ.symm ⟨e0123, e0123_mem⟩ * ⟨⁅v, a⁆, hwV⟩ := by
      apply S.frame.ψ.injective
      apply Subtype.ext
      rw [S.psi_zV, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, hwe]
      exact allOnes_eq_mul
    have heq := congrArg Subtype.val key
    simp only [Subgroup.coe_mul] at heq
    rw [heq]
    exact mul_mem (hV3Vh h0) hwVh
  have hVeq := NQS134.eq_of_zV_mem h331 h1222 S hzV
  apply hva
  rw [← hVh] at hVeq
  exact s134_comm_V S hv (hVeq ▸ haVh)

end CFSG.Quasithin.H13.U3
