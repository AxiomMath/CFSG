module

public import CFSG.Quasithin.MS93.S46R468Q2C

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

theorem inf_eq_bot_of_card_two {𝔾 : Type*} [Group 𝔾] {P Q : Subgroup 𝔾} (hP : Nat.card P = 2)
    (hQ : Nat.card Q = 2) (hPQ : P ≠ Q) : P ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  by_contra h1
  exact hPQ (eq_of_card_two_of_mem hP hQ ha.1 ha.2 h1)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem mem_bzero_of_forall_line (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {w : (puAmalgam c.pu.le).Universal}
    (hw : w ∈ Vv (puAmalgam c.pu.le) x)
    (h : ∀ k, (puAmalgam c.pu.le).treeGraph.Adj x k → ∀ v ∈ Vv (puAmalgam c.pu.le) k,
      ⁅w, v⁆ ∈ Zloc c.pu.le L x) : w ∈ bzero c x := by
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {v | v ∈ Vv (puAmalgam c.pu.le) x ∧ ⁅w, v⁆ ∈ Zloc c.pu.le L x}
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
  suffices hVS : Vv (puAmalgam c.pu.le) x ≤ S from ⟨hw, fun v hv => (hVS hv).2⟩
  rw [vv_eq_iSup_vv hx]
  exact iSup₂_le fun k hxk v hv => ⟨I466b.vv_le_vv_of_adj c.pu hx hxk hv, h k hxk v hv⟩

theorem commutator_mul_bzero_mem_zloc (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    {y b v : (puAmalgam c.pu.le).Universal} (hy : y ∈ Vv (puAmalgam c.pu.le) x)
    (hb : b ∈ bzero c x) (hv : v ∈ Vv (puAmalgam c.pu.le) x) (hyv : y * v = v * y) :
    ⁅y * b, v⁆ ∈ Zloc c.pu.le L x := by
  have e : ⁅y * b, v⁆ = y * ⁅b, v⁆ * y⁻¹ * ⁅y, v⁆ := by simp only [commutatorElement_def]; group
  rw [e, commutatorElement_eq_one_iff_mul_comm.mpr hyv, mul_one]
  exact (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x hy) _).mp (hb.2 v hv)

theorem mem_bzero_of_three (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {β x : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P₁ P₂ P₃ : Subgroup (puAmalgam c.pu.le).Universal} (h₁ : IsPtOn (puAmalgam c.pu.le) x β P₁)
    (h₂ : IsPtOn (puAmalgam c.pu.le) x β P₂) (h₃ : IsPtOn (puAmalgam c.pu.le) x β P₃)
    (n₁₂ : P₁ ≠ P₂) (n₁₃ : P₁ ≠ P₃) (n₂₃ : P₂ ≠ P₃) {w : (puAmalgam c.pu.le).Universal}
    (hw : w ∈ Vv (puAmalgam c.pu.le) x)
    (hP : ∀ P ∈ ({P₁, P₂, P₃} : Set (Subgroup (puAmalgam c.pu.le).Universal)),
      ∀ v ∈ pencil (puAmalgam c.pu.le) x P, ⁅w, v⁆ ∈ Zloc c.pu.le L x) : w ∈ bzero c x := by
  refine mem_bzero_of_forall_line c hx hw fun k hxk v hv => ?_
  rcases exists_pencil_of_three h464 h465 c hq hx hxβ h₁ h₂ h₃ n₁₂ n₁₃ n₂₃ hxk with h | h | h
  · exact hP P₁ (by simp) v (h hv)
  · exact hP P₂ (by simp) v (h hv)
  · exact hP P₃ (by simp) v (h hv)

theorem inv_mul_mem_zh_of_not_mem (h465 : I465) (c : Hyp46 M T L φ) (hq : Fintype.card F = 2)
    {γ β : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {w₁ w₂ : (puAmalgam c.pu.le).Universal}
    (hw₁ : w₁ ∈ ZM (puAmalgam c.pu.le) γ) (hw₂ : w₂ ∈ ZM (puAmalgam c.pu.le) γ)
    (hw₁β : w₁ ∉ ZH (puAmalgam c.pu.le) β) (hw₂β : w₂ ∉ ZH (puAmalgam c.pu.le) β) :
    w₁⁻¹ * w₂ ∈ ZH (puAmalgam c.pu.le) β := by
  have h2 : (ZH (puAmalgam c.pu.le) β).relIndex (ZM _ γ) = 2 := by
    rw [(h465 G M T L F φ c γ β hγ hγβ).2.1, hq]
  rcases mem_or_inv_mul_mem_of_relIndex_two h2 hw₁ hw₁β hw₂ with h | h
  · exact absurd h hw₂β
  · exact h

theorem false_of_two_active (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hγ : IsMVtx (puAmalgam c.pu.le) γ) (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β)
    (hZ : ¬ ZM (puAmalgam c.pu.le) γ ≤ bzero c α)
    (hidx : (Qv (puAmalgam c.pu.le) γ).relIndex (Vv _ α ⊔ Qv _ γ) = 2)
    {δ δ' : Subgroup (puAmalgam c.pu.le).Universal} (hδ : IsPtOn (puAmalgam c.pu.le) α β δ)
    (hδ' : IsPtOn (puAmalgam c.pu.le) α β δ') (hne : δ ≠ δ') {m m' : Vtx (puAmalgam c.pu.le)}
    (hαm : (puAmalgam c.pu.le).treeGraph.Adj α m) (hαm' : (puAmalgam c.pu.le).treeGraph.Adj α m')
    (hδm : δ ≤ Usup (puAmalgam c.pu.le) α m) (hδm' : δ' ≤ Usup (puAmalgam c.pu.le) α m')
    {y y' : (puAmalgam c.pu.le).Universal} (hy : y ∈ Vv (puAmalgam c.pu.le) m)
    (hyγ : y ∉ Qv (puAmalgam c.pu.le) γ) (hy' : y' ∈ Vv (puAmalgam c.pu.le) m')
    (hy'γ : y' ∉ Qv (puAmalgam c.pu.le) γ) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hVβγ : Vv (puAmalgam c.pu.le) β ≤ Qv _ γ :=
    vv_le_qv_of_adj_of_not_isMVtx hb hβ hγβ.symm
  have hδU : ∀ {P : Subgroup (puAmalgam c.pu.le).Universal},
      IsPtOn (puAmalgam c.pu.le) α β P → P ≤ Usup (puAmalgam c.pu.le) α β :=
    fun {P} ⟨_, _, _, hP⟩ => hP ▸ inf_le_left
  have hd2 : ∀ {k}, (puAmalgam c.pu.le).treeGraph.Adj α k →
      (puAmalgam c.pu.le).treeGraph.dist β k ≤ 2 := fun {k} hαk => by
    have h1 := dist_triangle (puAmalgam c.pu.le) β α k
    rw [tdist_comm (puAmalgam c.pu.le) β α, dist_eq_one_of_adj _ hαβ,
      dist_eq_one_of_adj _ hαk] at h1
    exact h1
  have hcen : ∀ {P : Subgroup (puAmalgam c.pu.le).Universal} {k : Vtx (puAmalgam c.pu.le)}
      {u : (puAmalgam c.pu.le).Universal}, IsPtOn (puAmalgam c.pu.le) α β P →
      (puAmalgam c.pu.le).treeGraph.Adj α k → P ≤ Usup (puAmalgam c.pu.le) α k →
      u ∈ Vv (puAmalgam c.pu.le) k → u ∉ Qv (puAmalgam c.pu.le) γ →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, u⁆ ∈ P ⊔ Zloc c.pu.le L α := by
    intro P k u hP hαk hPk hu huγ z hz
    have hk : ¬ IsMVtx (puAmalgam c.pu.le) k := (isMVtx_iff_of_adj _ hαk).mp hα
    have hkH : Usup (puAmalgam c.pu.le) α k ≠ Usup _ α β := fun he => huγ (hVβγ (by
      rw [vv_eq_of_usup_eq h464 h465 h466a c hα hαβ hαk he.symm]; exact hu))
    have hPc : Nat.card P = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ hP, hq]
    have hc := card_usup_inf_usup h464 h465 c hα hαβ hαk hkH.symm
    have : Finite ↥(Usup (puAmalgam c.pu.le) α β ⊓ Usup _ α k) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
    have hPe : P = Usup (puAmalgam c.pu.le) α β ⊓ Usup _ α k :=
      Subgroup.eq_of_le_of_card_ge (le_inf (hδU hP) hPk) (by rw [hc, hPc, hq])
    rw [hPe, ← zh_inf_zh_eq h464 h465 c hα hαβ hαk]
    exact commutator_vv_vv_le_zh_inf h464 c hβ hk (hd2 hαk)
      (Subgroup.commutator_mem_commutator (zm_le_vv_of_adj hγβ.symm hγ hz) hu)
  have hyV : y ∈ Vv (puAmalgam c.pu.le) α := I466b.vv_le_vv_of_adj c.pu hα hαm hy
  have hy'V : y' ∈ Vv (puAmalgam c.pu.le) α := I466b.vv_le_vv_of_adj c.pu hα hαm' hy'
  have hq₀ : ∀ v ∈ Vv (puAmalgam c.pu.le) α, v ∉ Qv (puAmalgam c.pu.le) γ →
      y⁻¹ * v ∈ Qv (puAmalgam c.pu.le) γ := fun v hv hvγ =>
    (mem_or_inv_mul_mem_of_relIndex_two hidx (Subgroup.mem_sup_left hyV) hyγ
      (Subgroup.mem_sup_left hv)).resolve_left hvγ
  have hcomm : ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ∀ t ∈ Qv (puAmalgam c.pu.le) γ, ⁅z, t⁆ = 1 :=
    fun z hz t ht => commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hγ hz) t ht).symm
  have hshift : ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      v ∉ Qv (puAmalgam c.pu.le) γ → ⁅z, v⁆ = ⁅z, y⁆ := fun z hz v hv hvγ => by
    calc ⁅z, v⁆ = ⁅z, y * (y⁻¹ * v)⁆ := by rw [mul_inv_cancel_left]
      _ = ⁅z, y⁆ := by
        rw [commutatorElement_mul_right', hcomm z hz _ (hq₀ v hv hvγ), mul_one, mul_inv_cancel,
          mul_one]
  have hδc : Nat.card δ = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ hδ, hq]
  have hδc' : Nat.card δ' = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ hδ', hq]
  have hUU := usup_le_uloc' c.pu hfull hα hαβ
  have hzZ : ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, y⁆ ∈ Zloc c.pu.le L α := fun z hz => by
    have h1 := hcen hδ hαm hδm hy hyγ z hz
    have h2 : ⁅z, y⁆ ∈ δ' ⊔ Zloc c.pu.le L α := by
      rw [← hshift z hz y' hy'V hy'γ]; exact hcen hδ' hαm' hδm' hy' hy'γ z hz
    exact sup_zloc_inf_sup_zloc_le c hα ((hδU hδ).trans hUU) ((hδU hδ').trans hUU)
      (inf_eq_bot_of_card_two hδc hδc' hne) ⟨h1, h2⟩
  apply hZ
  intro z hz
  refine ⟨I466b.vv_le_vv_of_adj c.pu hα hαβ (zm_le_vv_of_adj hγβ.symm hγ hz), fun v hv => ?_⟩
  by_cases hvγ : v ∈ Qv (puAmalgam c.pu.le) γ
  · rw [hcomm z hz v hvγ]; exact Subgroup.one_mem _
  · rw [hshift z hz v hv hvγ]; exact hzZ z hz

theorem le_usup_smul_of_qv (h464 : I464) (c : Hyp46 M T L φ) {α β m : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    {t : (puAmalgam c.pu.le).Universal} (htβ : t ∈ Qv (puAmalgam c.pu.le) β)
    {d : Subgroup (puAmalgam c.pu.le).Universal} (hdH : d ≤ Usup (puAmalgam c.pu.le) α β)
    (hdm : d ≤ Usup (puAmalgam c.pu.le) α m) (hmH : Usup (puAmalgam c.pu.le) α m ≠ Usup _ α β) :
    (puAmalgam c.pu.le).treeGraph.Adj α m → (puAmalgam c.pu.le).treeGraph.Adj α (t • m) ∧
      d ≤ Usup (puAmalgam c.pu.le) α (t • m) ∧ Usup (puAmalgam c.pu.le) α (t • m) ≠ Usup _ α β := by
  intro hαm
  have h464' := h464 G M T L F φ c
  have hts : t ∈ stab (puAmalgam c.pu.le) α := qv_le_stab_of_adj _ hαβ.symm htβ
  have htx : t • α = α := MulAction.mem_stabilizer_iff.mp hts
  have hU : Usup (puAmalgam c.pu.le) α (t • m) =
      (Usup (puAmalgam c.pu.le) α m).map (MulAut.conj t).toMonoidHom := by
    rw [← usup_smul, htx]
  have hcH : ∀ a ∈ Usup (puAmalgam c.pu.le) α β, t * a = a * t := fun a ha =>
    Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (h464' α β hα hαβ ha)) t htβ
  have hnH : t ∈ Subgroup.normalizer (Usup (puAmalgam c.pu.le) α β : Set _) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hcH a ha).symm)
  refine ⟨by have := (adj_smul _ t α m).mpr hαm; rwa [htx] at this, ?_, ?_⟩
  · rw [hU]
    intro a ha
    refine ⟨a, hdm ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcH a (hdH ha), mul_assoc, mul_inv_cancel, mul_one]
  · rw [hU]
    intro he
    rw [← map_conj_eq_of_mem_normalizer hnH] at he
    exact hmH (Subgroup.map_injective (MulAut.conj t).injective he)

theorem false_of_inactive_mem_ptQ (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hγ : IsMVtx (puAmalgam c.pu.le) γ) (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β)
    (hbad : ∀ μ A, (puAmalgam c.pu.le).treeGraph.Adj α μ → IsPtOn (puAmalgam c.pu.le) α μ A →
      ¬ ⁅Vv (puAmalgam c.pu.le) μ, ptQ _ α A⁆ ≤ bzero c α)
    {d d' : Subgroup (puAmalgam c.pu.le).Universal} (hd : IsPtOn (puAmalgam c.pu.le) α β d)
    (hd' : IsPtOn (puAmalgam c.pu.le) α β d') (hdd' : d ≠ d')
    (hin : ∀ m, (puAmalgam c.pu.le).treeGraph.Adj α m → d ≤ Usup (puAmalgam c.pu.le) α m →
      Vv (puAmalgam c.pu.le) m ≤ Qv _ γ)
    {z' : (puAmalgam c.pu.le).Universal} (hz'γ : z' ∈ Vv (puAmalgam c.pu.le) γ)
    (hz'β : z' ∈ Qv (puAmalgam c.pu.le) β) (hz'd : z' ∈ ptQ (puAmalgam c.pu.le) α d)
    (hz'α : z' ∉ Qv (puAmalgam c.pu.le) α) : False := by
  have hdc : Nat.card d = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ hd, hq]
  have : Finite ↥d := Nat.finite_of_card_ne_zero (by rw [hdc]; norm_num)
  have hdH : d ≤ Usup (puAmalgam c.pu.le) α β := by
    obtain ⟨_, _, _, hP⟩ := hd; exact hP ▸ inf_le_left
  have hde : ∀ {m}, (puAmalgam c.pu.le).treeGraph.Adj α m → d ≤ Usup (puAmalgam c.pu.le) α m →
      Usup (puAmalgam c.pu.le) α m ≠ Usup _ α β → d = Usup (puAmalgam c.pu.le) α β ⊓ Usup _ α m :=
    fun {m} hαm hdm hmH => by
      have hc := card_usup_inf_usup h464 h465 c hα hαβ hαm hmH.symm
      have : Finite ↥(Usup (puAmalgam c.pu.le) α β ⊓ Usup _ α m) :=
        Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
      exact Subgroup.eq_of_le_of_card_ge (le_inf hdH hdm) (by rw [hc, hdc, hq])
  obtain ⟨m₁, hαm₁, hne₁, hde₁⟩ := id hd
  have hdm₁ : d ≤ Usup (puAmalgam c.pu.le) α m₁ := hde₁ ▸ inf_le_right
  obtain ⟨t, ⟨htβ, htd'⟩, htα⟩ := exists_mem_qv_inf_ptQ h464 h465 h466a c hα hαβ hd'
  obtain ⟨hαm₂, hdm₂, hm₂H⟩ :=
    le_usup_smul_of_qv h464 c hα hαβ htβ hdH hdm₁ hne₁ hαm₁
  have hne₁₂ : Usup (puAmalgam c.pu.le) α (t • m₁) ≠ Usup _ α m₁ :=
    usup_smul_ne h464 h465 c hα hαβ hαm₁ (Ne.symm hne₁) hd' (by rw [← hde₁]; exact Ne.symm hdd')
      htβ htd' htα
  have hc₁₂ := card_usup_inf_usup h464 h465 c hα hαm₁ hαm₂ (Ne.symm hne₁₂)
  have : Finite ↥(Usup (puAmalgam c.pu.le) α m₁ ⊓ Usup _ α (t • m₁)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₁₂]; exact Fintype.card_ne_zero)
  have hde₁₂ : d = Usup (puAmalgam c.pu.le) α m₁ ⊓ Usup _ α (t • m₁) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hdm₁ hdm₂) (by rw [hc₁₂, hdc, hq])
  have hw : ∀ {m}, (puAmalgam c.pu.le).treeGraph.Adj α m → d ≤ Usup (puAmalgam c.pu.le) α m →
      Usup (puAmalgam c.pu.le) α m ≠ Usup _ α β →
      ∃ v ∈ Vv (puAmalgam c.pu.le) m, ⁅v, z'⁆ ∉ bzero c α := by
    intro m hαm hdm hmH
    by_contra h
    push Not at h
    have hdem := hde hαm hdm hmH
    have hle := commutator_vv_ptQ_le_bzero_of h464 h465 h466a c hq hα hαβ hαm (Ne.symm hmH)
      hz'β (hdem ▸ hz'd) hz'α h
    rw [← hdem] at hle
    exact hbad m d hαm ⟨β, hαβ, Ne.symm hmH, by rw [hdem, inf_comm]⟩ hle
  obtain ⟨v₁, hv₁, hv₁z⟩ := hw hαm₁ hdm₁ hne₁
  obtain ⟨v₂, hv₂, hv₂z⟩ := hw hαm₂ hdm₂ hm₂H
  have hwZ : ∀ {m}, (puAmalgam c.pu.le).treeGraph.Adj α m → d ≤ Usup (puAmalgam c.pu.le) α m →
      ∀ v ∈ Vv (puAmalgam c.pu.le) m, ⁅v, z'⁆ ∈ ZM (puAmalgam c.pu.le) γ := fun hαm hdm v hv =>
    (h465 G M T L F φ c γ β hγ hγβ).2.2 (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (hin _ hαm hdm hv) hz'γ)
  have hwV : ∀ {m}, (puAmalgam c.pu.le).treeGraph.Adj α m → d ≤ Usup (puAmalgam c.pu.le) α m →
      ∀ v ∈ Vv (puAmalgam c.pu.le) m, ⁅v, z'⁆ ∈ Vv (puAmalgam c.pu.le) m := by
    intro m hαm hdm v hv
    have hn := ptQ_le_normalizer_vv h464 h465 h466a c hα hαm hdm hz'd
    have e : ⁅v, z'⁆ = v * (z' * v * z'⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hv (Subgroup.inv_mem _ ((Subgroup.mem_normalizer_iff.mp hn v).mp hv))
  have hZβB : ZH (puAmalgam c.pu.le) β ≤ bzero c α := (zh_le_zm _ hαβ).trans (zm_le_bzero c hα)
  have h12 := inv_mul_mem_zh_of_not_mem h465 c hq hγ hγβ (hwZ hαm₂ hdm₂ v₂ hv₂)
    (hwZ hαm₁ hdm₁ v₁ hv₁) (fun h => hv₂z (hZβB h)) (fun h => hv₁z (hZβB h))
  apply hv₁z
  refine mem_bzero_of_mem_vv_mul h464 h465 c hq hα hαm₁ hαm₂ (Ne.symm hne₁₂)
    (hwV hαm₁ hdm₁ v₁ hv₁) (hwV hαm₂ hdm₂ v₂ hv₂) (hZβB h12) (by group) fun k hαk hk v hv => ?_
  rw [← hde₁₂] at hk
  have hO := commutator_vv_ptQ_le_centralizer_pencil h464 h465 h466a c hq hα hαm₁ hdm₁ hdc
  have hcv := Subgroup.mem_centralizer_iff.mp (hO (Subgroup.commutator_mem_commutator hv₁ hz'd))
    v (vv_le_pencil hαk hk hv)
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcv.symm]
  exact Subgroup.one_mem _

end CFSG.Quasithin.MS93.S46R
