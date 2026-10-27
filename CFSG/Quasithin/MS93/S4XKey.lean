module

public import CFSG.Quasithin.MS93.S4L42C
import CFSG.Quasithin.MS93.S34FCore
public import CFSG.Quasithin.MS93.S33SL
public import CFSG.Quasithin.MS93.S4L42B
public import CFSG.Quasithin.MS93.S4LCoreC

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

@[expose] def NoNonlinSLGt4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    4 < critDist (puAmalgam h.le) → IsSL3U M T L → ¬ IsSL3Full M T L → False

@[expose] def SLGt4Key : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    4 < critDist (puAmalgam h.le) → IsSL3U M T L → ¬ IsSL3Full M T L →
    ∃ E : Subgroup (puAmalgam h.le).Universal, E ≤ S34F.flat h (baseA _) ∧
      Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≠ ⊥ ∧
      ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
        ⁅Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal),
          Ltil h.le L δ⁆ ≤ ZM _ δ

section Conj

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] noncomputable def conjClosure (γ : Vtx X) (S : Subgroup X.Universal) :
    Subgroup X.Universal :=
  ⨆ g ∈ stab X γ, S.map (MulAut.conj g).toMonoidHom

variable {X}

theorem le_conjClosure (γ : Vtx X) (S : Subgroup X.Universal) : S ≤ conjClosure X γ S := by
  intro x hx
  have h1 : x ∈ S.map (MulAut.conj (1 : X.Universal)).toMonoidHom := ⟨x, hx, by simp⟩
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ stab X γ) => S.map (MulAut.conj g).toMonoidHom) 1
    (one_mem _) le_rfl h1

theorem conjClosure_le {γ : Vtx X} {S K : Subgroup X.Universal}
    (hK : ∀ g ∈ stab X γ, S.map (MulAut.conj g).toMonoidHom ≤ K) : conjClosure X γ S ≤ K :=
  iSup₂_le hK

theorem stab_le_normalizer_conjClosure (γ : Vtx X) (S : Subgroup X.Universal) :
    stab X γ ≤ Subgroup.normalizer (conjClosure X γ S : Set X.Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine conjClosure_le fun g' hg' => ?_
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g').toMonoidHom =
      (MulAut.conj (g * g')).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he]
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ stab X γ) => S.map (MulAut.conj g).toMonoidHom)
    (g * g') (mul_mem hg hg') le_rfl

end Conj

section Step

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hU : IsSL3U M T L)
include h hU

theorem le_uloc_sup_dloc_of_nonfull (hF : ¬ IsSL3Full M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {α β δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβδ : (puAmalgam h.le).treeGraph.Adj β δ)
    {K : Subgroup (puAmalgam h.le).Universal} (hKZ : K ≤ ZM _ δ)
    (hKL : ⁅K, Ltil h.le L α⁆ ≤ ZM _ α) : K ≤ Uloc h.le L α ⊔ Dloc h.le L α := by
  have h20 := h.hyp20
  have hβ : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hδ : IsMVtx (puAmalgam h.le) δ := by
    by_contra hδ
    exact hβ ((isMVtx_iff_of_adj _ hβδ).mpr hδ)
  have hQβα : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hQδβ : Qv (puAmalgam h.le) δ ≤ Qv _ β := qv_le_qv _ h20 hδ hβδ.symm
  have hQαβ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
  by_cases hQ : Qv (puAmalgam h.le) δ = Qv _ α
  · have hXδ : XM (puAmalgam h.le) δ = XM _ α := by
      unfold XM
      rw [hQ]
    refine hKZ.trans ((zm_le_xm _ h20 h.critDist_pos hδ).trans ?_)
    rw [hXδ, xm_eq_uloc_sup_zloc_of_isSL3U h hU hα]
    exact sup_le_sup_left (zloc_le_dloc h α) _
  obtain ⟨F, _, _, φ, hchar, hq, hφs, hnat⟩ := exists_natural_flat_of_nonfull h hU hF
  obtain ⟨ψ, hψs, hψ⟩ := S34F.exists_natural_flat_at h hφs hnat hα
  have hd : (puAmalgam h.le).treeGraph.dist δ α < critDist (puAmalgam h.le) := by
    have htri := dist_triangle (puAmalgam h.le) δ β α
    rw [tdist_comm _ δ β, dist_eq_one_of_adj _ hβδ, dist_eq_one_of_adj _ hαβ.symm] at htri
    omega
  intro w hw
  refine mem_uloc_sup_dloc_of_four_le h hU hα hq hψs hψ (zm_le_qv_of_dist_lt _ hδ hd (hKZ hw))
    (fun l hl => ?_) (Y := Qv _ δ) (hQδβ.trans hQβα) (fun y hy => ?_) ?_ ?_
  · rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hKL (Subgroup.commutator_mem_commutator hw hl))
  · exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hδ (hKZ hw)) y hy
  · exact hQαβ.trans ((qv_le_stab_of_adj _ hβδ).trans (stab_le_normalizer_qv _ δ))
  · intro hc
    apply hQ
    refine qv_eq_of_le h hα hδ ?_
    rw [← S43F.stab_inf_centralizer_uloc_of_isSL3U h hU hα]
    exact le_inf (hQδβ.trans hQβα) hc

end Step

section Linear

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hU : IsSL3U M T L)
include h hU

theorem le_sup_of_le_centralizer_ne_bot {E₀ : Subgroup G} (hE₀ : E₀ ≤ L ⊔ pCoreOf 2 M)
    {s₀ : G} (hs₀U : s₀ ∈ Uq M T L) (hs₀C : s₀ ∈ Subgroup.centralizer (E₀ : Set G))
    (hs₀1 : s₀ ≠ 1)
    (hT : T ≤ Subgroup.centralizer
      ((Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G) : Subgroup G) : Set G)) :
    T ≤ L ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, n, F, _, _, a, hcard, ha, -, -, β, hβ, hβker, hβα⟩ := hU
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) := h.le.trans hMV
  have hX : L ⊔ pCoreOf 2 M ≤ coordGroup β ⊤ M hMV := by
    refine sup_le (fun l hl => ?_) (fun x hx => ?_)
    · refine ⟨h.L_le hl, ⟨(a ⟨l, hl⟩ : GL (Fin 3) F), Subgroup.mem_top _⟩, ?_⟩
      intro u v huv
      simpa [moduleAct] using hβα ⟨l, hl⟩ u v huv 0
    · exact ⟨pCoreOf_le' M hx, (S34R.pCoreOf_le_linPart h β hx).2⟩
  set x₀ : Fin 3 → F := Multiplicative.toAdd (β ⟨s₀, hs₀U⟩) 0 with hx₀def
  have hx₀ : x₀ ≠ 0 := by
    intro h0
    apply hs₀1
    have hβ1 : β ⟨s₀, hs₀U⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact h0
    have hker : (⟨s₀, hs₀U⟩ : ↥(Uq M T L)) ∈ β.ker := hβ1
    rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hker
    exact hker
  have hscal : ∀ c : F, ∃ u : ↥(Uq M T L), Multiplicative.toAdd (β u) 0 = c • x₀ ∧
      (u : G) ∈ Subgroup.centralizer (E₀ : Set G) := by
    intro c
    obtain ⟨u, hu⟩ := exists_coord_eq hβ (c • x₀)
    refine ⟨u, hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨-, γ, hγ⟩ := hX (hE₀ he)
    have hes : e * s₀ * e⁻¹ = s₀ := by
      have := Subgroup.mem_centralizer_iff.mp hs₀C e he
      rw [this, mul_inv_cancel_right]
    have hfix : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x₀ = x₀ := by
      have := hγ ⟨s₀, hs₀U⟩ ⟨s₀, hs₀U⟩ hes.symm
      exact this.symm
    set v : ↥(Uq M T L) :=
      ⟨e * u * e⁻¹, conj_mem_of_mem_normalizer (hMV ((hE₀.trans (sup_le h.L_le
        (pCoreOf_le' M))) he)) u⟩ with hvdef
    have hv := hγ u v rfl
    rw [hu, Matrix.mulVec_smul, hfix, ← hu] at hv
    have hβv : β v = β u := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact hv
    have hvu : v = u := by
      have hk : v * u⁻¹ ∈ β.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hβv, mul_inv_cancel]
      rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hk
      exact mul_inv_eq_one.mp (Subtype.ext hk)
    have h1 : e * (u : G) * e⁻¹ = u := congrArg Subtype.val hvu
    calc e * (u : G) = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [h1]
  have hbot : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top]
    trivial
  intro t ht
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβ hβker (hTV ht)
  have hfix : ∀ c : F, f (c • x₀) = c • x₀ := by
    intro c
    obtain ⟨u, hu, huC⟩ := hscal c
    have htu : t * (u : G) * t⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp (hT ht) u ⟨u.2, huC⟩
      rw [← this, mul_inv_cancel_right]
    have := hf u u htu.symm
    rw [hu] at this
    exact this.symm
  have hl := S33.linear_of_fix h ha hβ hβker hβα (h.le ht) hf hx₀ hfix
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker (hTV ht) (hbot t) hf hl
  exact S34D.mem_sup_of_isCoordAct_sl h hcard ha hβ hβker hβα ht hγ

theorem sl3Full_of_qv_le_centralizer_ne_bot {E : Subgroup (puAmalgam h.le).Universal}
    (hEf : E ≤ S34F.flat h (baseA _))
    (hne : Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _) ≠ ⊥)
    (hT : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.centralizer
      ((Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _) : Subgroup _) : Set _)) :
    IsSL3Full M T L := by
  have hflat : S34F.flat h (baseA _) = imM h.le (L ⊔ pCoreOf 2 M) := by
    rw [S34F.flat, puTrans_baseA h.le (S34F.flat_subgroupOf_normal h)]
  have hEM : E ≤ imM h.le M :=
    hEf.trans (hflat.le.trans (imM_mono h.le (sup_le h.L_le (pCoreOf_le' M))))
  have himE : imM h.le (S33.pre h.le E) = E := S33.imM_pre h.le hEM
  have hE₀ : S33.pre h.le E ≤ L ⊔ pCoreOf 2 M := by
    intro x hx
    obtain ⟨m, hmE, rfl⟩ := (S33.mem_pre_iff' h.le).mp hx
    have hm := hEf hmE
    rw [hflat] at hm
    exact (S33.ofA_mem_imM_iff h.le m).mp hm
  have hUα : Uloc h.le L (baseA _) = imM h.le (Uq M T L) := by
    rw [Uloc, puTrans_baseA h.le (S4A.Uq_normal h)]
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun he => hx1 (Subtype.ext he)
  have hxU : x ∈ imM h.le (Uq M T L) := hUα ▸ hx.1
  obtain ⟨m, hmU, rfl⟩ := hxU
  have hs₀U : ((m : ↥M) : G) ∈ Uq M T L := Subgroup.mem_subgroupOf.mp hmU
  have hs₀C : ((m : ↥M) : G) ∈ Subgroup.centralizer (S33.pre h.le E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨m', hm'E, rfl⟩ := (S33.mem_pre_iff' h.le).mp he
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hm'E
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
  have hs₀1 : ((m : ↥M) : G) ≠ 1 := by
    intro he
    apply hx1'
    have : m = 1 := Subtype.ext he
    rw [this, map_one]
  set S₀ := Uq M T L ⊓ Subgroup.centralizer (S33.pre h.le E : Set G) with hS₀
  have hS₀M : S₀ ≤ M := inf_le_left.trans (Uq_le h.L_le)
  have himS : imM h.le S₀ ≤
      Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) := by
    refine le_inf ?_ ?_
    · rw [hUα]
      exact imM_mono h.le inf_le_left
    · rw [← himE]
      exact S34E.imM_le_centralizer h inf_le_right
  have hTS : T ≤ Subgroup.centralizer (S₀ : Set G) := by
    refine S34E.le_centralizer_of_imM h h.le hS₀M ?_
    rw [← puAmalgam.qv_baseB]
    exact hT.trans (Subgroup.centralizer_le himS)
  exact S34D.sl3Full_of_le_sup h hU
    (le_sup_of_le_centralizer_ne_bot h hU hE₀ hs₀U hs₀C hs₀1 hTS)

end Linear

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem map_conj_le_qv_baseB (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {S : Subgroup (puAmalgam h.le).Universal} (hSU : S ≤ Uloc h.le L (baseA _))
    {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) (baseB _)) :
    S.map (MulAut.conj g).toMonoidHom ≤ Qv (puAmalgam h.le) (baseB _) := by
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).mp hg
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (g • baseA _) := by
    have := (adj_smul (puAmalgam h.le) g (baseB _) (baseA _)).mpr hαβ.symm
    rwa [hgβ] at this
  have hδM : IsMVtx (puAmalgam h.le) (g • baseA _) := by
    have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  have hd : (puAmalgam h.le).treeGraph.dist (g • baseA _) (baseB _) <
      critDist (puAmalgam h.le) := by
    rw [dist_eq_one_of_adj _ hβδ.symm]
    omega
  refine (Subgroup.map_mono hSU).trans ?_
  show (puTrans h.le (Uq M T L) (baseA _)).map (MulAut.conj g).toMonoidHom ≤ _
  rw [← puTrans_smul h.le (S4A.Uq_normal h)]
  exact (S34F.uloc_le_zm' h hδM).trans (zm_le_qv_of_dist_lt _ hδM hd)

theorem map_conj_le_uloc_sup_dloc (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hF : ¬ IsSL3Full M T L) (hb : 2 < critDist (puAmalgam h.le))
    {S : Subgroup (puAmalgam h.le).Universal} (hSU : S ≤ Uloc h.le L (baseA _))
    (hSL : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ → ⁅S, Ltil h.le L δ⁆ ≤ ZM _ δ)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab (puAmalgam h.le) (baseB _)) :
    S.map (MulAut.conj g).toMonoidHom ≤ Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) := by
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).mp hg
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (g • baseA _) := by
    have := (adj_smul (puAmalgam h.le) g (baseB _) (baseA _)).mpr hαβ.symm
    rwa [hgβ] at this
  have hβδ' : (puAmalgam h.le).treeGraph.Adj (baseB _) (g⁻¹ • baseA _) := by
    have := (adj_smul (puAmalgam h.le) g⁻¹ (baseB _) (baseA _)).mpr hαβ.symm
    rwa [inv_smul_eq_iff.mpr hgβ.symm] at this
  have hδM : IsMVtx (puAmalgam h.le) (g • baseA _) := by
    have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  refine le_uloc_sup_dloc_of_nonfull h hU hF hb hα hαβ hβδ ?_ ?_
  · refine (Subgroup.map_mono hSU).trans ?_
    show (puTrans h.le (Uq M T L) (baseA _)).map (MulAut.conj g).toMonoidHom ≤ _
    rw [← puTrans_smul h.le (S4A.Uq_normal h)]
    exact S34F.uloc_le_zm' h hδM
  · have hL : Ltil h.le L (baseA _) =
        (Ltil h.le L (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      show puTrans h.le L (baseA _) = (puTrans h.le L (g⁻¹ • baseA _)).map _
      rw [← puTrans_smul h.le (S4A.L_normal h), smul_inv_smul]
    have hZ : ZM (puAmalgam h.le) (baseA _) =
        (ZM (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← PU.zm_smul, smul_inv_smul]
    rw [hL, ← Subgroup.map_commutator, hZ]
    exact Subgroup.map_mono (hSL _ hβδ')

theorem noNonlinSLGt4_of_key (hK : SLGt4Key) : NoNonlinSLGt4 := by
  intro G _ _ M T L h hmin hb hU hF
  obtain ⟨E, hEf, hne, hSL⟩ := hK G M T L h hmin hb hU hF
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  set S := Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)
    with hS
  have hWT : conjClosure (puAmalgam h.le) (baseB _) S ≤ Qv (puAmalgam h.le) (baseB _) :=
    conjClosure_le fun g hg => map_conj_le_qv_baseB h hb2 inf_le_left hg
  have hW : conjClosure (puAmalgam h.le) (baseB _) S ≤
      Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) :=
    conjClosure_le fun g hg => map_conj_le_uloc_sup_dloc h hU hF hb2 inf_le_left hSL hg
  have hcen := Core.qv_le_centralizer_of_le_uloc_sup_dloc h hmin hU hWT
    (stab_le_normalizer_conjClosure (baseB _) S) hW
  exact hF (sl3Full_of_qv_le_centralizer_ne_bot h hU hEf hne
    (hcen.trans (Subgroup.centralizer_le (le_conjClosure (baseB _) S))))

end Main

end CFSG.Quasithin.MS93.S4L
