module

public import CFSG.Quasithin.MS93.S46R468Q2B
public import CFSG.Quasithin.MS93.S46R468C4A
public import CFSG.Quasithin.MS93.S46R468Q2A

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commute_ptQ_of_isPtOn (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x ℓ P) {r p : (puAmalgam c.pu.le).Universal}
    (hr : r ∈ ptQ (puAmalgam c.pu.le) x P) (hp : p ∈ P) : r * p = p * r := by
  obtain ⟨ψ, -, hψU, hPc, -⟩ := exists_coord_pt h464 h465 h466a c hx hxℓ hP
  have hPU : P ≤ Uloc c.pu.le L x := le_uloc_of_isPtOn c hx hP
  obtain ⟨hrs, hrE⟩ := ptQ_le_ptL c hx hψU hPU hPc hr
  have hpU := hPU hp
  have hmem : r * p * r⁻¹ ∈ Uloc c.pu.le L x :=
    (Subgroup.mem_normalizer_iff.mp (hψU.1 hrs) p).mp hpU
  have h1 := natVec_conj hψU ⟨r, hrs⟩ ⟨p, hpU⟩ ⟨_, hmem⟩ rfl
  have hp0 := (hPc ⟨p, hpU⟩).mp hp
  have he : natVec hψU ⟨p, hpU⟩ =
      (natVec hψU ⟨p, hpU⟩ 0) • (Pi.single 0 1 : Fin 3 → F) := by
    ext i
    fin_cases i
    · simp
    · simp [hp0.1]
    · simp [hp0.2]
  have hE : ((toSL3 ψ ⟨r, hrs⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 := hrE
  have h2 : natVec hψU ⟨_, hmem⟩ = natVec hψU ⟨p, hpU⟩ := by
    rw [h1, he, Matrix.mulVec_smul, hE]
  have h3 : r * p * r⁻¹ = p := congrArg Subtype.val (natVec_injective hψU h2)
  calc r * p = r * p * r⁻¹ * r := by group
    _ = p * r := by rw [h3]

theorem commute_vv_commutator_vv_ptQ' (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x k m : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxk : (puAmalgam c.pu.le).treeGraph.Adj x k)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x k ≠ Usup _ x m) {u v r : (puAmalgam c.pu.le).Universal}
    (hu : u ∈ Vv (puAmalgam c.pu.le) k) (hv : v ∈ Vv (puAmalgam c.pu.le) m)
    (hr : r ∈ ptQ (puAmalgam c.pu.le) x (Usup _ x k ⊓ Usup _ x m)) :
    u * ⁅v, r⁆ = ⁅v, r⁆ * u := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have h464' := h464 G M T L F φ c
  set P := Usup (puAmalgam c.pu.le) x k ⊓ Usup _ x m with hPdef
  have hPk : IsPtOn (puAmalgam c.pu.le) x k P := ⟨m, hxm, Ne.symm hne, rfl⟩
  have hk : ¬ IsMVtx (puAmalgam c.pu.le) k := (isMVtx_iff_of_adj _ hxk).mp hx
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hVk := I466b.vv_le_vv_of_adj c.pu hx hxk
  have hVm := I466b.vv_le_vv_of_adj c.pu hx hxm
  refine le_of_commute_commutator (A := Vv _ k) (B := Vv _ m) (K := ptQ _ x P)
    (S₁ := Qv _ k ⊓ ptQ _ x P) (S₂ := Qv _ m ⊓ ptQ _ x P)
    (ptQ_le_normalizer_vv h464 h465 h466a c hx hxk inf_le_left)
    (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm inf_le_right)
    (ptQ_le_sup_qv_inf h464 h465 h466a c hx hxk hxm hne rfl) inf_le_right inf_le_right
    ?_ ?_ r hr v hv u hu
  · rintro r ⟨hrk, hrP⟩ v hv u hu
    have hv' : r * v * r⁻¹ ∈ Vv (puAmalgam c.pu.le) m :=
      (Subgroup.mem_normalizer_iff.mp
        (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm inf_le_right hrP) v).mp hv
    have e0 : ⁅v, r⁆ = v * (r * v * r⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    have hd : (puAmalgam c.pu.le).treeGraph.dist k m ≤ 2 := by
      have h1 := dist_triangle (puAmalgam c.pu.le) k x m
      rw [tdist_comm (puAmalgam c.pu.le) k x, dist_eq_one_of_adj _ hxk,
        dist_eq_one_of_adj _ hxm] at h1
      exact h1
    have hz : ⁅u, r⁆ ∈ ZM (puAmalgam c.pu.le) x :=
      zh_le_zm _ hxk (commutator_vv_qv_le_zh c.pu h464' hk
        (Subgroup.commutator_mem_commutator hu hrk))
    have hc₁ : ⁅u, v⁆ ∈ ZH (puAmalgam c.pu.le) k ⊓ ZH _ m :=
      commutator_vv_vv_le_zh_inf h464 c hk hm hd (Subgroup.commutator_mem_commutator hu hv)
    have hc₁x : ⁅u, v⁆ ∈ ZM (puAmalgam c.pu.le) x := zh_le_zm _ hxk hc₁.1
    have hc₁P : ⁅u, v⁆ ∈ P ⊔ Zloc c.pu.le L x := by
      rw [← zh_inf_zh_eq h464 h465 c hx hxk hxm]; exact hc₁
    have hrs : r ∈ stab (puAmalgam c.pu.le) x := (mem_ptQ.mp hrP).1
    have hcen : P ⊔ Zloc c.pu.le L x ≤ Subgroup.centralizer ({r} : Set _) := by
      refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
        (fun z hz => Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
      · rw [Set.mem_singleton_iff.mp hg]
        exact commute_ptQ_of_isPtOn h464 h465 h466a c hx hxk hPk hrP hp
      · rw [Set.mem_singleton_iff.mp hg]
        exact Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hx hz) r hrs
    have hrc : r * ⁅u, v⁆ * r⁻¹ = ⁅u, v⁆ := by
      have := Subgroup.mem_centralizer_iff.mp (hcen hc₁P) r rfl
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
    have hzu : Commute ⁅u, r⁆ u := commute_zm_vv c.pu hb hx hz (hVk hu)
    have hzv' : Commute ⁅u, r⁆ (r * v * r⁻¹) := commute_zm_vv c.pu hb hx hz (hVm hv')
    have hcv : Commute ⁅u, v⁆ v := commute_zm_vv c.pu hb hx hc₁x (hVm hv)
    have hcv' : Commute ⁅u, v⁆ (r * v * r⁻¹) := commute_zm_vv c.pu hb hx hc₁x (hVm hv')
    have e4 : r * u * r⁻¹ = ⁅u, r⁆⁻¹ * u := by rw [commutatorElement_def]; group
    have hzw : Commute ⁅u, r⁆ (u * (r * v * r⁻¹) * u⁻¹) :=
      (hzu.mul_right hzv').mul_right hzu.inv_right
    have e3 : ⁅u, r * v * r⁻¹⁆ = ⁅u, v⁆ := by
      calc ⁅u, r * v * r⁻¹⁆
          = ⁅u, r⁆⁻¹ * ((u * (r * v * r⁻¹) * u⁻¹) * ⁅u, r⁆) * (r * v * r⁻¹)⁻¹ := by
            rw [← hzw.eq, commutatorElement_def]; group
        _ = ⁅⁅u, r⁆⁻¹ * u, r * v * r⁻¹⁆ := by rw [commutatorElement_def]; group
        _ = ⁅r * u * r⁻¹, r * v * r⁻¹⁆ := by rw [e4]
        _ = r * ⁅u, v⁆ * r⁻¹ := by simp only [commutatorElement_def]; group
        _ = ⁅u, v⁆ := hrc
    have huv : u * v * u⁻¹ = ⁅u, v⁆ * v := by rw [commutatorElement_def]; group
    have huv' : u * (r * v * r⁻¹) * u⁻¹ = ⁅u, v⁆ * (r * v * r⁻¹) := by
      rw [← e3, commutatorElement_def]; group
    have hcw : Commute ⁅u, v⁆ (v * (r * v * r⁻¹)⁻¹) := hcv.mul_right hcv'.inv_right
    rw [e0]
    calc u * (v * (r * v * r⁻¹)⁻¹)
        = (u * v * u⁻¹) * (u * (r * v * r⁻¹) * u⁻¹)⁻¹ * u := by group
      _ = (⁅u, v⁆ * v) * (⁅u, v⁆ * (r * v * r⁻¹))⁻¹ * u := by rw [huv, huv']
      _ = (⁅u, v⁆ * (v * (r * v * r⁻¹)⁻¹)) * ⁅u, v⁆⁻¹ * u := by group
      _ = ((v * (r * v * r⁻¹)⁻¹) * ⁅u, v⁆) * ⁅u, v⁆⁻¹ * u := by rw [hcw.eq]
      _ = (v * (r * v * r⁻¹)⁻¹) * u := by group
  · rintro r ⟨hrm, -⟩ v hv u hu
    have hz : ⁅v, r⁆ ∈ ZM (puAmalgam c.pu.le) x :=
      zh_le_zm _ hxm (commutator_vv_qv_le_zh c.pu h464' hm
        (Subgroup.commutator_mem_commutator hv hrm))
    exact (commute_zm_vv c.pu hb hx hz (hVk hu)).symm

theorem inf_eq_bot_of_not_le_usup (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x m k : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m) (hxk : (puAmalgam c.pu.le).treeGraph.Adj x k)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x m P)
    (hPk : ¬ P ≤ Usup (puAmalgam c.pu.le) x k) : P ⊓ Usup (puAmalgam c.pu.le) x k = ⊥ := by
  have hPm : P ≤ Usup (puAmalgam c.pu.le) x m := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  by_cases hmk : Usup (puAmalgam c.pu.le) x m = Usup _ x k
  · exact absurd (hmk ▸ hPm) hPk
  have hP' : IsPtOn (puAmalgam c.pu.le) x m (Usup _ x m ⊓ Usup _ x k) :=
    ⟨k, hxk, Ne.symm hmk, rfl⟩
  have hne : P ≠ Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x k := fun he =>
    hPk (he ▸ inf_le_right)
  have hbot := inf_eq_bot_of_isPtOn h464 h465 c hx hxm hP hP' hne
  rw [eq_bot_iff, ← hbot]
  exact le_inf inf_le_left (le_inf (inf_le_left.trans hPm) inf_le_right)

theorem mem_bzero_of_mem_vv_mul' (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x m m' : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hxm' : (puAmalgam c.pu.le).treeGraph.Adj x m')
    (hne : Usup (puAmalgam c.pu.le) x m ≠ Usup _ x m') {w w' b : (puAmalgam c.pu.le).Universal}
    (hw : w ∈ Vv (puAmalgam c.pu.le) m) (hw' : w' ∈ Vv (puAmalgam c.pu.le) m')
    (hb : b ∈ bzero c x) (hwe : w = w' * b)
    (hP : ∀ k, (puAmalgam c.pu.le).treeGraph.Adj x k →
      Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x m' ≤ Usup _ x k →
      ∀ v ∈ Vv (puAmalgam c.pu.le) k, ⁅w, v⁆ ∈ Zloc c.pu.le L x) :
    w ∈ bzero c x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  set P := Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x m' with hPdef
  have hPpt : IsPtOn (puAmalgam c.pu.le) x m P := ⟨m', hxm', Ne.symm hne, rfl⟩
  set Z := Zloc c.pu.le L x with hZdef
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hm' : ¬ IsMVtx (puAmalgam c.pu.le) m' := (isMVtx_iff_of_adj _ hxm').mp hx
  have hwV : w ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxm hw
  have hw'V : w' ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxm' hw'
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {v | v ∈ Vv (puAmalgam c.pu.le) x ∧ ⁅w, v⁆ ∈ Z}
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', ?_⟩
        have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ha' ((Subgroup.mem_normalizer_iff.mp
          (vv_le_normalizer_zloc c x ha) _).mp hb'')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x
          (Subgroup.inv_mem _ ha)) _).mp (Subgroup.inv_mem _ ha') }
  suffices hVS : Vv (puAmalgam c.pu.le) x ≤ S from ⟨hwV, fun v hv => (hVS hv).2⟩
  rw [vv_eq_iSup_vv hx]
  refine iSup₂_le fun k hxk => fun v hv => ⟨I466b.vv_le_vv_of_adj c.pu hx hxk hv, ?_⟩
  by_cases hPk : P ≤ Usup (puAmalgam c.pu.le) x k
  · exact hP k hxk hPk v hv
  have hk : ¬ IsMVtx (puAmalgam c.pu.le) k := (isMVtx_iff_of_adj _ hxk).mp hx
  have hvV : v ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxk hv
  have hd : ∀ {ρ}, (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      (puAmalgam c.pu.le).treeGraph.dist ρ k ≤ 2 := fun {ρ} hxρ => by
    have h1 := dist_triangle (puAmalgam c.pu.le) ρ x k
    rw [tdist_comm (puAmalgam c.pu.le) ρ x, dist_eq_one_of_adj _ hxρ,
      dist_eq_one_of_adj _ hxk] at h1
    exact h1
  have h1 : ⁅w, v⁆ ∈ (Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x k) ⊔ Z := by
    rw [← zh_inf_zh_eq h464 h465 c hx hxm hxk]
    exact commutator_vv_vv_le_zh_inf h464 c hm hk (hd hxm)
      (Subgroup.commutator_mem_commutator hw hv)
  have h2 : ⁅w, v⁆ ∈ (Usup (puAmalgam c.pu.le) x m' ⊓ Usup _ x k) ⊔ Z := by
    have e : ⁅w' * b, v⁆ = (w' * ⁅b, v⁆ * w'⁻¹) * ⁅w', v⁆ := by
      simp only [commutatorElement_def]; group
    have hbv : w' * ⁅b, v⁆ * w'⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x hw'V) _).mp (hb.2 v hvV)
    have hw'v : ⁅w', v⁆ ∈ (Usup (puAmalgam c.pu.le) x m' ⊓ Usup _ x k) ⊔ Z := by
      rw [← zh_inf_zh_eq h464 h465 c hx hxm' hxk]
      exact commutator_vv_vv_le_zh_inf h464 c hm' hk (hd hxm')
        (Subgroup.commutator_mem_commutator hw' hv)
    rw [hwe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hbv) hw'v
  have hPk' : P ⊓ Usup (puAmalgam c.pu.le) x k = ⊥ :=
    inf_eq_bot_of_not_le_usup h464 h465 c hx hxm hxk hPpt hPk
  have hA₁₂ : (Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x k) ⊓ (Usup _ x m' ⊓ Usup _ x k) = ⊥ :=
    le_bot_iff.mp (le_trans (le_inf (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right)) hPk'.le)
  exact sup_zloc_inf_sup_zloc_le c hx (inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxm))
    (inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxm')) hA₁₂ ⟨h1, h2⟩

theorem uloc_inf_sup_zloc (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {A : Subgroup (puAmalgam c.pu.le).Universal}
    (hA : A ≤ Uloc c.pu.le L x) : (A ⊔ Zloc c.pu.le L x) ⊓ Uloc c.pu.le L x = A := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hZc : Zloc c.pu.le L x ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) x : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hx
  have hUs : Uloc c.pu.le L x ≤ stab (puAmalgam c.pu.le) x := puTrans_le_stab c.pu.le _ x
  have hnZ : A ≤ Subgroup.normalizer (Zloc c.pu.le L x : Set _) :=
    (hA.trans hUs).trans ((Subgroup.le_centralizer_iff.mp hZc).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [S45.sup_inf_eq_of_le hA hnZ, inf_comm, uloc_inf_zloc c.pu hfull x, sup_bot_eq]

theorem uloc_inf_zh (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) :
    ZH (puAmalgam c.pu.le) β ⊓ Uloc c.pu.le L x = Usup (puAmalgam c.pu.le) x β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  rw [zh_eq_usup_sup_zloc c.pu c.via h464' hsq hx hxβ]
  exact uloc_inf_sup_zloc c hx (usup_le_uloc' c.pu hfull hx hxβ)

theorem usup_le_of_isPtOn_ne (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P P' S : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    (hP' : IsPtOn (puAmalgam c.pu.le) x β P') (hne : P ≠ P') (hPS : P ≤ S) (hP'S : P' ≤ S) :
    Usup (puAmalgam c.pu.le) x β ≤ S := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hPU : P ≤ Usup (puAmalgam c.pu.le) x β := by
    obtain ⟨_, _, _, he⟩ := hP; rw [he]; exact inf_le_left
  have hP'U : P' ≤ Usup (puAmalgam c.pu.le) x β := by
    obtain ⟨_, _, _, he⟩ := hP'; rw [he]; exact inf_le_left
  have hUZ : Usup (puAmalgam c.pu.le) x β ≤ ZM _ x :=
    (usup_le_uloc' c.pu hfull hx hxβ).trans (uloc_le_zm c.pu hfull hx)
  have hcomm : P' ≤ Subgroup.centralizer (P : Set (puAmalgam c.pu.le).Universal) :=
    fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      commute_of_mem_zm c hx (hUZ (hPU hb)) (hUZ (hP'U ha))
  have hcard : Nat.card ↥(P ⊔ P') = Nat.card ↥(Usup (puAmalgam c.pu.le) x β) := by
    rw [card_sup_of_commute hcomm (inf_eq_bot_of_isPtOn h464 h465 c hx hxβ hP hP' hne),
      card_of_isPtOn h464 h465 c hx hxβ hP, card_of_isPtOn h464 h465 c hx hxβ hP',
      (h465 G M T L F φ c x β hx hxβ).1, sq]
  have : Finite ↥(Usup (puAmalgam c.pu.le) x β) := Nat.finite_of_card_ne_zero (by
    rw [(h465 G M T L F φ c x β hx hxβ).1]; exact pow_ne_zero 2 Fintype.card_ne_zero)
  have heq : P ⊔ P' = Usup (puAmalgam c.pu.le) x β :=
    Subgroup.eq_of_le_of_card_ge (sup_le hPU hP'U) hcard.ge
  rw [← heq]
  exact sup_le hPS hP'S

end CFSG.Quasithin.MS93.S46R
