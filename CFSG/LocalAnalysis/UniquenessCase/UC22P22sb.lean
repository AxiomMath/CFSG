module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xn
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.RankThree.PartOne (omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x
open scoped Matrix

namespace P22s

section SL2

variable {F : Type} [Field F] [Finite F]

theorem sl2_sub_mem_span {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (g : ↥(StatedSL 2 F))
    {w₀ : Fin 2 → F} (hw₀ : w₀ ≠ 0)
    (hg : (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ = w₀) (v : Fin 2 → F) :
    (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v - v ∈ Submodule.span F {w₀} := by
  haveI := Fintype.ofFinite F
  set A : Matrix (Fin 2) (Fin 2) F := (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) with hA
  have hAA : A * A = 1 := sl2_stab_mul_self hF hn g hw₀ hg
  have h2 : (2 : F) = 0 := two_eq_zero_of_card hF hn
  by_cases hA1 : A = 1
  · rw [hA1, Matrix.one_mulVec, sub_self]
    exact Submodule.zero_mem _
  set K : Submodule F (Fin 2 → F) := LinearMap.ker (Matrix.toLin' A - LinearMap.id) with hK
  have hmemK : ∀ x : Fin 2 → F, x ∈ K ↔ A *ᵥ x = x := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_zero]
  have hKtop : K ≠ ⊤ := by
    intro hK1
    apply hA1
    have hlin : Matrix.toLin' A = Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) F) := by
      refine LinearMap.ext fun x => ?_
      rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
      exact (hmemK x).1 (hK1 ▸ Submodule.mem_top)
    exact Matrix.toLin'.injective hlin
  have hspan : Submodule.span F {w₀} ≤ K := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (hmemK w₀).2 hg
  have hfin : Module.finrank F K ≤ Module.finrank F (Submodule.span F {w₀}) := by
    have h1 := Submodule.finrank_lt hKtop
    rw [Module.finrank_fin_fun] at h1
    rw [finrank_span_singleton hw₀]
    omega
  have heq : Submodule.span F {w₀} = K := Submodule.eq_of_le_of_finrank_le hspan hfin
  rw [heq, hmemK]
  have hmv : A *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  rw [Matrix.mulVec_sub, hmv]
  have : (2 : F) • (v - A *ᵥ v) = 0 := by rw [h2, zero_smul]
  rw [two_smul] at this
  linear_combination (exp := 1) this

theorem sl2_mulVec_sub_eq_zero {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (g h : ↥(StatedSL 2 F))
    {w₀ : Fin 2 → F} (hw₀ : w₀ ≠ 0)
    (hg : (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ = w₀)
    (hh : (((h : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ = w₀) (v : Fin 2 → F) :
    (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((((h : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v - v) -
      ((((h : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v - v) = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (sl2_sub_mem_span hF hn h hw₀ hh v)
  rw [← hc, Matrix.mulVec_smul, hg, sub_self]

end SL2

end P22s

namespace P22x

section Module

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.commOn_sub_mem_natC (d : NatDec ρ Nbar Nb) (i : Fin m) {Q : Subgroup X} (hQN : Q ≤ Nbar)
    (hQ2 : IsPGroup 2 Q) {w : V} (hw : w ∈ commOn ρ Q (natIi ρ Nbar (Nb i))) {a : X} (ha : a ∈ Q) :
    ρ a w - w ∈ natC ρ Nbar := by
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  set P : Subgroup X := d.proj i Q with hP
  have hP2 : IsPGroup 2 P := d.isPGroup_proj i hQ2
  set Q' : Subgroup ↥(StatedSL 2 F) := (P.subgroupOf (Nb i)).map φ.toMonoidHom with hQ'def
  have hQ'2 : IsPGroup 2 Q' := (hP2.comap_subtype).map _
  obtain ⟨w₀, hw₀, hw₀fix⟩ := exists_ne_zero_mem_sl2Fix hF hn Q' hQ'2
  have hPle : P ≤ Nb i := d.proj_le i Q
  have hmemQ' : ∀ (b : X) (hb : b ∈ P), φ ⟨b, hPle hb⟩ ∈ Q' := by
    intro b hb
    exact Subgroup.mem_map_of_mem _ (show (⟨b, hPle hb⟩ : ↥(Nb i)) ∈ P.subgroupOf (Nb i) from hb)
  obtain ⟨f, rfl⟩ := d.exists_natPi (hQN ha)
  have hfP : ((f i : ↥(Nb i)) : X) ∈ P := (d.mem_proj i).2 ⟨f, ha, rfl⟩
  have hIi : ∀ x ∈ natIi ρ Nbar (Nb i), ∀ g ∈ Nbar, ρ g x ∈ natIi ρ Nbar (Nb i) :=
    fun x hx g hg => d.inv_Ii hg i x hx
  have hW : commOn ρ Q (natIi ρ Nbar (Nb i)) ≤ natIi ρ Nbar (Nb i) :=
    commOn_le_of_invariant fun b hb u hu => hIi u hu b (hQN hb)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, y, hy, rfl⟩ := hx
    obtain ⟨f', rfl⟩ := d.exists_natPi (hQN hb)
    have hf'P : ((f' i : ↥(Nb i)) : X) ∈ P := (d.mem_proj i).2 ⟨f', hb, rfl⟩
    have hby : ρ (d.natPi f') y = ρ ((f' i : ↥(Nb i)) : X) y := d.pi_act f' i hy
    have hz : ρ (d.natPi f') y - y ∈ natIi ρ Nbar (Nb i) :=
      (natIi ρ Nbar (Nb i)).sub_mem (hIi y hy _ (hQN hb)) hy
    have haz := d.pi_act f i hz
    set t := ρ (d.natPi f) (ρ (d.natPi f') y - y) - (ρ (d.natPi f') y - y) with ht
    have htI : t ∈ natIi ρ Nbar (Nb i) := (natIi ρ Nbar (Nb i)).sub_mem (hIi _ hz _ (hQN ha)) hz
    have hψt : ψ t = 0 := by
      rw [ht, haz, hby, map_sub, hψφ (f i) _ (by rw [← hby]; exact hz), map_sub, hψφ (f' i) y hy]
      have hg := hw₀fix _ (hmemQ' _ hfP)
      have hh := hw₀fix _ (hmemQ' _ hf'P)
      exact P22s.sl2_mulVec_sub_eq_zero hF hn _ _ hw₀ hg hh (ψ y)
    exact (hψA t htI hψt).2
  | zero => simp only [map_zero, sub_zero]; exact (natC ρ Nbar).zero_mem
  | add x y _ _ hx hy =>
    have : ρ (d.natPi f) (x + y) - (x + y) =
        (ρ (d.natPi f) x - x) + (ρ (d.natPi f) y - y) := by rw [map_add]; abel
    rw [this]
    exact (natC ρ Nbar).add_mem hx hy
  | smul c x _ hx =>
    have : ρ (d.natPi f) (c • x) - c • x = c • (ρ (d.natPi f) x - x) := by
      rw [map_smul, smul_sub]
    rw [this]
    exact (natC ρ Nbar).smul_mem c hx

end Module

end P22x

variable {G : Type} [Group G] [Finite G]

theorem uc22p22sb_jOf_le_centralizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) :
    jOf D.T ≤ centralizer (proofEiHat D (preN D (Nb i)) : Set G) := by
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  set Q : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (jOf D.T) with hQdef
  have hQN : Q ≤ mbarImage D.M D.U (proofN D) := mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hQ2 : IsPGroup 2 Q :=
    ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype (K := D.M)).map _
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzU : z ∈ D.U := proofEiHat_le D (preN_le_M D (Nb i)) hz
  obtain ⟨u, rfl⟩ := exists_iota e hzU
  have hu : u ∈ commOn ρ Q (natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i)) := by
    have := mem_bsub.2 hz
    rwa [bsub_proofEiHat D e ρ hc (d.le i)] at this
  have huI : u ∈ natI ρ (mbarImage D.M D.U (proofN D)) :=
    d.Ii_le_I i (commOn_le_of_invariant (fun b hb v hv => d.inv_Ii (hQN hb) i v hv) hu)
  have hjM : j ∈ D.M := D.sylowM.le ((uc22p22e_jOf_le_self D.T) hj)
  have hfix : ρ (QuotientGroup.mk ⟨j, hjM⟩) u = u :=
    uc22p22xf_imgEI_of D Ch h2 h3 h51 hH c Umod e ρ hc u huI
      (fun a ha => d.commOn_sub_mem_natC i hQN hQ2 hu ha) _ ⟨⟨j, hjM⟩, hj, rfl⟩
  have h1 := iota_rho hV e ρ hc ⟨j, hjM⟩ u
  rw [hfix] at h1
  calc iota e u * j = (j * iota e u * j⁻¹) * j := by rw [← h1]
    _ = j * iota e u := by group

theorem uc22p22sb_proofEiHat_le_proofE (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) :
    proofEiHat D (preN D (Nb i)) ≤ proofE D := by
  intro z hz
  have hzU : z ∈ D.U := proofEiHat_le D (preN_le_M D (Nb i)) hz
  have hJ := uc22p22sb_jOf_le_centralizer D Ch h2 h3 h51 hH c m Nb hNb i
  refine uc22p22e_mem_omegaZJ'.2 ⟨uc22p22xf_UleT D hzU, fun j hj => ?_, (uc22p22xf_hel D).2 z hzU⟩
  exact ((Subgroup.mem_centralizer_iff.1 (hJ hj)) z hz).symm

theorem uc22p22sb_proofS_le_centralizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) :
    proofS D ≤ centralizer (proofEiHat D (preN D (Nb i)) : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le (uc22p22sb_proofEiHat_le_proofE D Ch h2 h3 h51 hH c m Nb hNb i))

theorem uc22p22sb_U_le_proofS (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) : D.U ≤ proofS D := by
  have hE := uc22p22xf_eleCU_of D Ch h2 h3 h51 hH c
  refine le_inf (uc22p22xf_UleT D) (fun u hu => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((Subgroup.mem_centralizer_iff.1 (hE hz)) u hu).symm

theorem uc22p22sb_proofEiHat_le_omegaOneCenterIn (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) :
    proofEiHat D (preN D (Nb i)) ≤ omegaOneCenterIn (proofS D) := by
  intro z hz
  have hzU : z ∈ D.U := proofEiHat_le D (preN_le_M D (Nb i)) hz
  have hzS : z ∈ proofS D := uc22p22sb_U_le_proofS D Ch h2 h3 h51 hH c hzU
  have hcen := uc22p22sb_proofS_le_centralizer D Ch h2 h3 h51 hH c m Nb hNb i
  have hzc : (⟨z, hzS⟩ : ↥(proofS D)) ∈ Subgroup.center ↥(proofS D) :=
    Subgroup.mem_center_iff.2 fun s => Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hcen s.2)) z hz).symm
  exact Subgroup.subset_closure ⟨⟨⟨z, hzS⟩, hzc, rfl⟩, (uc22p22xf_hel D).2 z hzU⟩

theorem uc22p22sb_not_preN_le_centralizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) :
    ¬ preN D (Nb i) ≤ centralizer (proofEiHat D (preN D (Nb i)) : Set G) := by
  intro hcon
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbar
  set Q : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (jOf D.T) with hQdef
  set W : Submodule (ZMod 2) Umod := commOn ρ Q (natIi ρ Nbar (Nb i)) with hW
  set C : Submodule (ZMod 2) Umod := natC ρ Nbar with hC
  have hQN : Q ≤ Nbar := mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hfixW : ∀ h ∈ Nb i, ∀ u ∈ W, ρ h u = u := by
    intro h hh u hu
    have hhN : h ∈ mbarImage D.M D.U (preN D (Nb i)) := by rwa [mbarImage_preN D (d.le i)]
    obtain ⟨x, hx, rfl⟩ := hhN
    have hz : iota e u ∈ proofEiHat D (preN D (Nb i)) := by
      have : u ∈ bsub e (proofEiHat D (preN D (Nb i))) := by
        rw [bsub_proofEiHat D e ρ hc (d.le i)]
        exact hu
      exact mem_bsub.1 this
    have hxc : iota e u * (x : G) = (x : G) * iota e u :=
      (Subgroup.mem_centralizer_iff.1 (hcon hx)) _ hz
    apply iota_injective e
    rw [QuotientGroup.mk'_apply, iota_rho hV e ρ hc x u]
    calc (x : G) * iota e u * (x : G)⁻¹ = iota e u * x * (x : G)⁻¹ := by rw [← hxc]
      _ = iota e u := by group
  obtain ⟨y₀, hy₀W, hy₀I, hy₀C⟩ : ∃ y₀ ∈ W, y₀ ∈ natIi ρ Nbar (Nb i) ∧ y₀ ∉ C := by
    obtain ⟨A', hA'max, hne⟩ := NatDec.exists_isMax_proj_ne_bot D d i
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hbQ : (b : MBar D.M D.U) ∈ d.proj i Q :=
      d.proj_mono i (mbarImage_mono D.M D.U (le_jOf_of_isMax hA'max)) b.2
    have hbN : (b : MBar D.M D.U) ∈ Nb i := d.proj_le i _ b.2
    have hb1' : (b : MBar D.M D.U) ≠ 1 := fun h => hb1 (Subtype.ext h)
    by_contra hall
    push Not at hall
    apply hb1'
    refine d.faithful_modC (d.le i hbN) fun j y hy => ?_
    by_cases hji : j = i
    · subst hji
      obtain ⟨a, ha, hay⟩ := d.exists_act_of_proj j hbQ hy
      have hyW : ρ a y - y ∈ W := sub_mem_commOn ha hy
      have hyI : ρ a y - y ∈ natIi ρ Nbar (Nb j) :=
        (natIi ρ Nbar (Nb j)).sub_mem (d.inv_Ii (hQN ha) j y hy) hy
      rw [← hay]
      exact hall _ hyW hyI
    · rw [d.lemma21 (Ne.symm hji) hbN hy, sub_self]
      exact C.zero_mem
  have hYinv : ∀ h ∈ Nb i, ∀ v ∈ W ⊔ C, ρ h v ∈ W ⊔ C := by
    intro h hh v hv
    obtain ⟨w, hw, c', hc', rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hfixW h hh w hw, natC_fix (d.le i hh) hc']
    exact Submodule.add_mem_sup hw hc'
  have hIY : natIi ρ Nbar (Nb i) ≤ W ⊔ C :=
    d.irr i le_sup_right hYinv hy₀I (Submodule.mem_sup_left hy₀W) hy₀C
  apply d.ne_bot i
  rw [eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_bot]
  refine d.faithful i hh fun v hv => ?_
  obtain ⟨w, hw, c', hc', hwc⟩ := Submodule.mem_sup.1 (hIY hv)
  rw [← hwc, map_add, hfixW h hh w hw, natC_fix (d.le i hh) hc']

end CFSG.LocalAnalysis.UniquenessCase.UC22
