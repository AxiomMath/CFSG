module

public import CFSG.Quasithin.MS93.S46R468Q2D

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

theorem mem_normalizer_of_map_conj_eq {𝔾 : Type*} [Group 𝔾] {K : Subgroup 𝔾} {g : 𝔾}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set 𝔾) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [← h]
    exact ⟨k, hk, rfl⟩
  · intro hk
    rw [← h] at hk
    obtain ⟨k', hk', he'⟩ := hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at he'
    rwa [← he']

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem usup_smul_ne_of_not_mem_ptQ (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {α β n : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hαn : (puAmalgam c.pu.le).treeGraph.Adj α n) {d : Subgroup (puAmalgam c.pu.le).Universal}
    (hd : IsPtOn (puAmalgam c.pu.le) α β d) (hdn : d ≤ Usup (puAmalgam c.pu.le) α n)
    (hnH : Usup (puAmalgam c.pu.le) α n ≠ Usup _ α β) {z' : (puAmalgam c.pu.le).Universal}
    (hz'β : z' ∈ Qv (puAmalgam c.pu.le) β) (hz'd : z' ∉ ptQ (puAmalgam c.pu.le) α d) :
    Usup (puAmalgam c.pu.le) α (z' • n) ≠ Usup _ α n := by
  intro he
  have hzs : z' ∈ stab (puAmalgam c.pu.le) α := qv_le_stab_of_adj _ hαβ.symm hz'β
  have hzx : z' • α = α := MulAction.mem_stabilizer_iff.mp hzs
  have hn : z' ∈ Subgroup.normalizer (Usup (puAmalgam c.pu.le) α n : Set _) :=
    mem_normalizer_of_map_conj_eq (by rw [← usup_smul, hzx]; exact he)
  have hP := mem_ptQ_of_mem_normalizer_usup h464 h465 c hα hαβ hαn (Ne.symm hnH) hz'β hn
  have hdc : Nat.card d = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ hd, hq]
  have hc := card_usup_inf_usup h464 h465 c hα hαβ hαn (Ne.symm hnH)
  have : Finite ↥(Usup (puAmalgam c.pu.le) α β ⊓ Usup _ α n) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
  have hdH : d ≤ Usup (puAmalgam c.pu.le) α β := by
    obtain ⟨_, _, _, hP⟩ := hd; exact hP ▸ inf_le_left
  have hde : d = Usup (puAmalgam c.pu.le) α β ⊓ Usup _ α n :=
    Subgroup.eq_of_le_of_card_ge (le_inf hdH hdn) (by rw [hc, hdc, hq])
  exact hz'd (hde ▸ hP)

theorem commutator_vv_ptQ_le_vv (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {α n : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαn : (puAmalgam c.pu.le).treeGraph.Adj α n) {d : Subgroup (puAmalgam c.pu.le).Universal}
    (hdn : d ≤ Usup (puAmalgam c.pu.le) α n) :
    ⁅Vv (puAmalgam c.pu.le) n, ptQ _ α d⁆ ≤ Vv (puAmalgam c.pu.le) n := by
  refine Subgroup.commutator_le.mpr fun v hv r hr => ?_
  have hn := ptQ_le_normalizer_vv h464 h465 h466a c hα hαn hdn hr
  have e : ⁅v, r⁆ = v * (r * v * r⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ hv (Subgroup.inv_mem _ ((Subgroup.mem_normalizer_iff.mp hn v).mp hv))

theorem mem_bzero_of_commutator_mem_bzero (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {α β n : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hαn : (puAmalgam c.pu.le).treeGraph.Adj α n) {d : Subgroup (puAmalgam c.pu.le).Universal}
    (hd : IsPtOn (puAmalgam c.pu.le) α β d) (hdn : d ≤ Usup (puAmalgam c.pu.le) α n)
    (hnH : Usup (puAmalgam c.pu.le) α n ≠ Usup _ α β) {z' : (puAmalgam c.pu.le).Universal}
    (hz'β : z' ∈ Qv (puAmalgam c.pu.le) β) (hz'd : z' ∉ ptQ (puAmalgam c.pu.le) α d)
    {a : (puAmalgam c.pu.le).Universal} (ha : a ∈ ⁅Vv (puAmalgam c.pu.le) n, ptQ _ α d⁆)
    (haz : ⁅a, z'⁆ ∈ bzero c α) : a ∈ bzero c α := by
  have hdc : Nat.card d = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ hd, hq]
  have : Finite ↥d := Nat.finite_of_card_ne_zero (by rw [hdc]; norm_num)
  have hdH : d ≤ Usup (puAmalgam c.pu.le) α β := by
    obtain ⟨_, _, _, hP⟩ := hd; exact hP ▸ inf_le_left
  obtain ⟨hαn', hdn', -⟩ := le_usup_smul_of_qv h464 c hα hαβ hz'β hdH hdn hnH hαn
  have hne := usup_smul_ne_of_not_mem_ptQ h464 h465 c hq hα hαβ hαn hd hdn hnH hz'β hz'd
  have haV := commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαn hdn ha
  have hVn' : Vv (puAmalgam c.pu.le) (z' • n) =
      (Vv (puAmalgam c.pu.le) n).map (MulAut.conj z').toMonoidHom := vi_smul _ z' n 2
  have hw' : z' * a * z'⁻¹ ∈ Vv (puAmalgam c.pu.le) (z' • n) := by
    rw [hVn']; exact ⟨a, haV, rfl⟩
  have has : a ∈ stab (puAmalgam c.pu.le) α :=
    vv_le_stab_self c α (I466b.vv_le_vv_of_adj c.pu hα hαn haV)
  have hb : (z' * a * z'⁻¹)⁻¹ * a ∈ bzero c α := by
    have e : (z' * a * z'⁻¹)⁻¹ * a = a⁻¹ * ⁅a, z'⁆ * a⁻¹⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c α
      (Subgroup.inv_mem _ has)) _).mp haz
  have hc := card_usup_inf_usup h464 h465 c hα hαn hαn' (Ne.symm hne)
  have : Finite ↥(Usup (puAmalgam c.pu.le) α n ⊓ Usup _ α (z' • n)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
  have hde : d = Usup (puAmalgam c.pu.le) α n ⊓ Usup _ α (z' • n) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hdn hdn') (by rw [hc, hdc, hq])
  refine mem_bzero_of_mem_vv_mul h464 h465 c hq hα hαn hαn' (Ne.symm hne) haV hw' hb
    (by group) fun k hαk hk v hv => ?_
  rw [← hde] at hk
  have hO := commutator_vv_ptQ_le_centralizer_pencil h464 h465 h466a c hq hα hαn hdn hdc
  have hcv := Subgroup.mem_centralizer_iff.mp (hO ha) v (vv_le_pencil hαk hk hv)
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcv.symm]
  exact Subgroup.one_mem _

theorem inv_mul_mem_bzero_of_inactive (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {α β γ n : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hγ : IsMVtx (puAmalgam c.pu.le) γ) (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β)
    (hαn : (puAmalgam c.pu.le).treeGraph.Adj α n) {d : Subgroup (puAmalgam c.pu.le).Universal}
    (hd : IsPtOn (puAmalgam c.pu.le) α β d) (hdn : d ≤ Usup (puAmalgam c.pu.le) α n)
    (hnH : Usup (puAmalgam c.pu.le) α n ≠ Usup _ α β) (hin : Vv (puAmalgam c.pu.le) n ≤ Qv _ γ)
    {z' : (puAmalgam c.pu.le).Universal} (hz'γ : z' ∈ Vv (puAmalgam c.pu.le) γ)
    (hz'β : z' ∈ Qv (puAmalgam c.pu.le) β) (hz'd : z' ∉ ptQ (puAmalgam c.pu.le) α d)
    {a a' : (puAmalgam c.pu.le).Universal} (ha : a ∈ ⁅Vv (puAmalgam c.pu.le) n, ptQ _ α d⁆)
    (ha' : a' ∈ ⁅Vv (puAmalgam c.pu.le) n, ptQ _ α d⁆) (haB : a ∉ bzero c α)
    (ha'B : a' ∉ bzero c α) : a⁻¹ * a' ∈ bzero c α := by
  have hZβB : ZH (puAmalgam c.pu.le) β ≤ bzero c α := (zh_le_zm _ hαβ).trans (zm_le_bzero c hα)
  have hzγ : ∀ {b}, b ∈ ⁅Vv (puAmalgam c.pu.le) n, ptQ _ α d⁆ → ⁅b, z'⁆ ∈ ZM _ γ :=
    fun {b} hb => (h465 G M T L F φ c γ β hγ hγβ).2.2 (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator
        (hin (commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαn hdn hb)) hz'γ)
  have hnB : ∀ {b}, b ∈ ⁅Vv (puAmalgam c.pu.le) n, ptQ _ α d⁆ → b ∉ bzero c α →
      ⁅b, z'⁆ ∉ ZH (puAmalgam c.pu.le) β := fun {b} hb hbB h =>
    hbB (mem_bzero_of_commutator_mem_bzero h464 h465 h466a c hq hα hαβ hαn hd hdn hnH hz'β
      hz'd hb (hZβB h))
  have h12 := inv_mul_mem_zh_of_not_mem h465 c hq hγ hγβ (hzγ ha) (hzγ ha') (hnB ha haB)
    (hnB ha' ha'B)
  have hcomm : ⁅a, z'⁆ * ⁅a', z'⁆ = ⁅a', z'⁆ * ⁅a, z'⁆ :=
    commute_of_mem_zm c hγ (hzγ ha) (hzγ ha')
  have has : a ∈ stab (puAmalgam c.pu.le) α := vv_le_stab_self c α
    (I466b.vv_le_vv_of_adj c.pu hα hαn (commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαn hdn ha))
  have hmem : ⁅a⁻¹ * a', z'⁆ ∈ bzero c α := by
    have e : ⁅a⁻¹ * a', z'⁆ = a⁻¹ * (⁅a, z'⁆⁻¹ * ⁅a', z'⁆) * a⁻¹⁻¹ := by
      have e1 : ⁅a', z'⁆ * ⁅a, z'⁆⁻¹ = ⁅a, z'⁆⁻¹ * ⁅a', z'⁆ :=
        ((Commute.inv_left (show Commute ⁅a, z'⁆ ⁅a', z'⁆ from hcomm)).eq).symm
      rw [← e1]
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c α
      (Subgroup.inv_mem _ has)) _).mp (hZβB h12)
  exact mem_bzero_of_commutator_mem_bzero h464 h465 h466a c hq hα hαβ hαn hd hdn hnH hz'β hz'd
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) ha') hmem

theorem sup_eq_of_card_two_of_card_four {𝔾 : Type*} [Group 𝔾] {H P₁ P₂ : Subgroup 𝔾}
    (hH : Nat.card H = 4) (h₁ : P₁ ≤ H) (h₂ : P₂ ≤ H) (c₁ : Nat.card P₁ = 2)
    (c₂ : Nat.card P₂ = 2) (n₁₂ : P₁ ≠ P₂) : P₁ ⊔ P₂ = H := by
  have : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have hle : P₁ ⊔ P₂ ≤ H := sup_le h₁ h₂
  have : Finite ↥(P₁ ⊔ P₂) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hdvd : Nat.card ↥(P₁ ⊔ P₂) ∣ 4 := hH ▸ Subgroup.card_dvd_of_le hle
  have hge : 2 ≤ Nat.card ↥(P₁ ⊔ P₂) := c₁ ▸ Subgroup.card_le_of_le le_sup_left
  have hne : Nat.card ↥(P₁ ⊔ P₂) ≠ 2 := fun h => n₁₂ (by
    have e1 : P₁ = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, c₁])
    have e2 : P₂ = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, c₂])
    rw [e1, ← e2])
  have h4 : Nat.card ↥(P₁ ⊔ P₂) = 4 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(P₁ ⊔ P₂) <;> first | rfl | omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hH])

theorem conj_mem_centralizer_map {𝔾 : Type*} [Group 𝔾] {K : Subgroup 𝔾} {b : 𝔾}
    (hb : b ∈ Subgroup.centralizer (K : Set 𝔾)) (g : 𝔾) :
    g * b * g⁻¹ ∈ Subgroup.centralizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup 𝔾) :
      Set 𝔾) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have h := Subgroup.mem_centralizer_iff.mp hb k hk
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * k * g⁻¹ * (g * b * g⁻¹) = g * (k * b) * g⁻¹ := by group
    _ = g * (b * k) * g⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * (g * k * g⁻¹) := by group

theorem conj_mem_commutator_of_mem_normalizer {𝔾 : Type*} [Group 𝔾] {A B : Subgroup 𝔾} {g x : 𝔾}
    (hA : g ∈ Subgroup.normalizer (A : Set 𝔾)) (hB : g ∈ Subgroup.normalizer (B : Set 𝔾))
    (hx : x ∈ ⁅A, B⁆) : g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  have h : (⁅A, B⁆ : Subgroup 𝔾).map (MulAut.conj g).toMonoidHom = ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hA,
      map_conj_eq_of_mem_normalizer hB]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem commutator_mem_centralizer_pencil (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {α m : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαm : (puAmalgam c.pu.le).treeGraph.Adj α m)
    {d : Subgroup (puAmalgam c.pu.le).Universal} (hdm : d ≤ Usup (puAmalgam c.pu.le) α m)
    (hdc : Nat.card d = 2) {b t : (puAmalgam c.pu.le).Universal}
    (hb : b ∈ ⁅Vv (puAmalgam c.pu.le) m, ptQ _ α d⁆) (ht : t ∈ stab (puAmalgam c.pu.le) α)
    (htd : t ∈ Subgroup.normalizer (d : Set (puAmalgam c.pu.le).Universal)) :
    ⁅b, t⁆ ∈ Subgroup.centralizer (pencil (puAmalgam c.pu.le) α d : Set _) := by
  have hO := commutator_vv_ptQ_le_centralizer_pencil h464 h465 h466a c hq hα hαm hdm hdc hb
  have htx : t • α = α := MulAction.mem_stabilizer_iff.mp ht
  have hY : (pencil (puAmalgam c.pu.le) α d).map (MulAut.conj t).toMonoidHom =
      pencil (puAmalgam c.pu.le) α d := by
    rw [← pencil_smul, htx, map_conj_eq_of_mem_normalizer htd]
  have h1 := conj_mem_centralizer_map hO t
  rw [hY] at h1
  have e : ⁅b, t⁆ = b * (t * b * t⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ hO (Subgroup.inv_mem _ h1)

theorem isPtOn_map_conj_ne (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {α β n : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hαn : (puAmalgam c.pu.le).treeGraph.Adj α n) {d₁ d₂ : Subgroup (puAmalgam c.pu.le).Universal}
    (h₁ : IsPtOn (puAmalgam c.pu.le) α β d₁) (h₂ : IsPtOn (puAmalgam c.pu.le) α β d₂)
    (n₁₂ : d₁ ≠ d₂) (hnH : Usup (puAmalgam c.pu.le) α n ≠ Usup _ α β)
    {g : (puAmalgam c.pu.le).Universal}
    (hgn : g ∈ Qv (puAmalgam c.pu.le) n) (hgd : g ∈ ptQ (puAmalgam c.pu.le) α d₂)
    (hgα : g ∉ Qv (puAmalgam c.pu.le) α) :
    IsPtOn (puAmalgam c.pu.le) α β (d₁.map (MulAut.conj g).toMonoidHom) ∧
      d₁.map (MulAut.conj g).toMonoidHom ≠ d₁ ∧ d₁.map (MulAut.conj g).toMonoidHom ≠ d₂ := by
  have h464' := h464 G M T L F φ c
  have hgs : g ∈ stab (puAmalgam c.pu.le) α := (mem_ptQ.mp hgd).1
  have hgx : g • α = α := MulAction.mem_stabilizer_iff.mp hgs
  have hdH : ∀ {P}, IsPtOn (puAmalgam c.pu.le) α β P → P ≤ Usup (puAmalgam c.pu.le) α β :=
    fun {P} ⟨_, _, _, hP⟩ => hP ▸ inf_le_left
  have hgT := ptQ_le_normalizer_qv h464 h465 h466a c hα hαβ (hdH h₂) hgd
  have hT : Qv (puAmalgam c.pu.le) (g • β) = Qv _ β := by
    rw [qv_smul]; exact map_conj_eq_of_mem_normalizer hgT
  have hH : (Usup (puAmalgam c.pu.le) α β).map (MulAut.conj g).toMonoidHom = Usup _ α β := by
    rw [← usup_smul, hgx]
    show ⁅Zv (puAmalgam c.pu.le) α, Qv _ (g • β)⁆ = ⁅Zv (puAmalgam c.pu.le) α, Qv _ β⁆
    rw [hT]
  have hinj := (MulAut.conj g).injective
  have hd₂g : d₂.map (MulAut.conj g).toMonoidHom = d₂ :=
    map_conj_eq_of_mem_normalizer (mem_ptQ.mp hgd).2.1
  refine ⟨?_, fun he => ?_, fun he => n₁₂ (Subgroup.map_injective hinj (he.trans hd₂g.symm))⟩
  · obtain ⟨m, hαm, hne, hde⟩ := h₁
    have hαgm : (puAmalgam c.pu.le).treeGraph.Adj α (g • m) := by
      have := (adj_smul _ g α m).mpr hαm; rwa [hgx] at this
    have hUgm : Usup (puAmalgam c.pu.le) α (g • m) =
        (Usup (puAmalgam c.pu.le) α m).map (MulAut.conj g).toMonoidHom := by
      rw [← usup_smul, hgx]
    refine ⟨g • m, hαgm, fun he => hne ?_, ?_⟩
    · rw [hUgm, ← hH] at he
      exact Subgroup.map_injective hinj he
    · rw [hde, Subgroup.map_inf _ _ _ hinj, hH, hUgm]
  ·
    have hgd₁ : g ∈ Subgroup.normalizer (d₁ : Set (puAmalgam c.pu.le).Universal) :=
      mem_normalizer_of_map_conj_eq he
    have hc₁ : Nat.card d₁ = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ h₁, hq]
    have hc₂ : Nat.card d₂ = 2 := by rw [card_of_isPtOn h464 h465 c hα hαβ h₂, hq]
    have hc4 : Nat.card ↥(Usup (puAmalgam c.pu.le) α β) = 4 := by
      rw [(h465 G M T L F φ c α β hα hαβ).1, hq]; norm_num
    have hsup := sup_eq_of_card_two_of_card_four hc4 (hdH h₁) (hdH h₂) hc₁ hc₂ n₁₂
    have hcen : ∀ {P : Subgroup (puAmalgam c.pu.le).Universal}, Nat.card P = 2 →
        g ∈ Subgroup.normalizer (P : Set _) → P ≤ Subgroup.centralizer ({g} : Set _) :=
      fun {P} hP hgP p hp => Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        have := conj_eq_of_mem_normalizer_of_card_two hP hgP hp
        calc g * p = g * p * g⁻¹ * g := by group
          _ = p * g := by rw [this]
    have hHc : Usup (puAmalgam c.pu.le) α β ≤ Subgroup.centralizer ({g} : Set _) := by
      rw [← hsup]
      exact sup_le (hcen hc₁ hgd₁) (hcen hc₂ (mem_ptQ.mp hgd).2.1)
    have hnc : Usup (puAmalgam c.pu.le) α n ≤ Subgroup.centralizer ({g} : Set _) :=
      fun u hu => Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        exact Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ n (h464' α n hα hαn hu)) g hgn
    have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
    have hU := uloc_le_usup_sup_usup h464 h465 c hα hαβ hαn hnH.symm
    have hZc : ZM (puAmalgam c.pu.le) α ≤ Subgroup.centralizer ({g} : Set _) := by
      rw [zm_eq_uloc_sup_zloc c.pu hfull hα]
      refine sup_le ((hU.trans (sup_le hHc hnc))) fun z hz =>
        Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hα hz) g hgs
    have hgc : g ∈ Subgroup.centralizer (ZM (puAmalgam c.pu.le) α : Set _) :=
      Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp (hZc hu) g rfl).symm
    apply hgα
    rw [← c.pu.centHyp α n hα hαn]
    exact ⟨hgn, hgc⟩

theorem false_of_two_inactive (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    (hγ : IsMVtx (puAmalgam c.pu.le) γ) (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β)
    (hbad : ∀ μ A, (puAmalgam c.pu.le).treeGraph.Adj α μ → IsPtOn (puAmalgam c.pu.le) α μ A →
      ¬ ⁅Vv (puAmalgam c.pu.le) μ, ptQ _ α A⁆ ≤ bzero c α)
    {d₁ d₂ d₃ : Subgroup (puAmalgam c.pu.le).Universal} (h₁ : IsPtOn (puAmalgam c.pu.le) α β d₁)
    (h₂ : IsPtOn (puAmalgam c.pu.le) α β d₂) (h₃ : IsPtOn (puAmalgam c.pu.le) α β d₃)
    (n₁₂ : d₁ ≠ d₂) (n₁₃ : d₁ ≠ d₃) (n₂₃ : d₂ ≠ d₃)
    (hin₁ : ∀ m, (puAmalgam c.pu.le).treeGraph.Adj α m → d₁ ≤ Usup (puAmalgam c.pu.le) α m →
      Vv (puAmalgam c.pu.le) m ≤ Qv _ γ)
    (hin₂ : ∀ m, (puAmalgam c.pu.le).treeGraph.Adj α m → d₂ ≤ Usup (puAmalgam c.pu.le) α m →
      Vv (puAmalgam c.pu.le) m ≤ Qv _ γ)
    {z' : (puAmalgam c.pu.le).Universal} (hz'γ : z' ∈ Vv (puAmalgam c.pu.le) γ)
    (hz'β : z' ∈ Qv (puAmalgam c.pu.le) β) (hz'₁ : z' ∉ ptQ (puAmalgam c.pu.le) α d₁)
    (hz'₂ : z' ∉ ptQ (puAmalgam c.pu.le) α d₂) : False := by
  have h464' := h464 G M T L F φ c
  have hZβB : ZH (puAmalgam c.pu.le) β ≤ bzero c α := (zh_le_zm _ hαβ).trans (zm_le_bzero c hα)
  have hzs : z' ∈ stab (puAmalgam c.pu.le) α := qv_le_stab_of_adj _ hαβ.symm hz'β
  have hdH : ∀ {P}, IsPtOn (puAmalgam c.pu.le) α β P → P ≤ Usup (puAmalgam c.pu.le) α β :=
    fun {P} ⟨_, _, _, hP⟩ => hP ▸ inf_le_left
  have hcard : ∀ {P}, IsPtOn (puAmalgam c.pu.le) α β P → Nat.card ↥P = 2 := fun {P} hP => by
    rw [card_of_isPtOn h464 h465 c hα hαβ hP, hq]
  have hz'n : ∀ {P}, IsPtOn (puAmalgam c.pu.le) α β P →
      z' ∈ Subgroup.normalizer (P : Set (puAmalgam c.pu.le).Universal) := fun {P} hP =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (h464' α β hα hαβ (hdH hP ha)))
        z' hz'β).symm)
  have hnQ : ∀ {t : (puAmalgam c.pu.le).Universal} {P : Subgroup (puAmalgam c.pu.le).Universal},
      t ∈ stab (puAmalgam c.pu.le) α → t ∈ Subgroup.normalizer (P : Set _) →
      t ∈ Subgroup.normalizer (ptQ (puAmalgam c.pu.le) α P : Set _) := fun {t P} ht htP =>
    mem_normalizer_of_map_conj_eq (by
      rw [← ptQ_smul, MulAction.mem_stabilizer_iff.mp ht, map_conj_eq_of_mem_normalizer htP])
  have hVs : ∀ {t}, t ∈ stab (puAmalgam c.pu.le) α →
      t ∈ Subgroup.normalizer (Vv (puAmalgam c.pu.le) α : Set _) := fun {t} ht =>
    stab_le_normalizer_of_smul _ (fun g δ => vi_smul _ g δ 2) α ht
  obtain ⟨m₁, hαm₁, hne₁, hde₁⟩ := id h₁
  obtain ⟨n₀, hαn₀, hne₀, hde₀⟩ := id h₂
  have hd₁m₁ : d₁ ≤ Usup (puAmalgam c.pu.le) α m₁ := hde₁ ▸ inf_le_right
  have hd₂n₀ : d₂ ≤ Usup (puAmalgam c.pu.le) α n₀ := hde₀ ▸ inf_le_right
  have hpt₁ : IsPtOn (puAmalgam c.pu.le) α m₁ d₁ := ⟨β, hαβ, Ne.symm hne₁, by rw [hde₁, inf_comm]⟩
  have hpt₂ : IsPtOn (puAmalgam c.pu.le) α n₀ d₂ := ⟨β, hαβ, Ne.symm hne₀, by rw [hde₀, inf_comm]⟩
  obtain ⟨b₀, hb₀, hb₀B⟩ := IsConcreteLE.not_le_iff_exists.mp (hbad m₁ d₁ hαm₁ hpt₁)
  obtain ⟨a₀, ha₀, ha₀B⟩ := IsConcreteLE.not_le_iff_exists.mp (hbad n₀ d₂ hαn₀ hpt₂)
  have hx : ∀ {m : Vtx (puAmalgam c.pu.le)} {d : Subgroup (puAmalgam c.pu.le).Universal}
      {a : (puAmalgam c.pu.le).Universal}, (puAmalgam c.pu.le).treeGraph.Adj α m →
      IsPtOn (puAmalgam c.pu.le) α β d → d ≤ Usup (puAmalgam c.pu.le) α m →
      Usup (puAmalgam c.pu.le) α m ≠ Usup _ α β → Vv (puAmalgam c.pu.le) m ≤ Qv _ γ →
      z' ∉ ptQ (puAmalgam c.pu.le) α d → a ∈ ⁅Vv (puAmalgam c.pu.le) m, ptQ _ α d⁆ →
      a ∉ bzero c α → ⁅a, z'⁆ ∈ ZM (puAmalgam c.pu.le) γ ∧ ⁅a, z'⁆ ∉ bzero c α := by
    intro m d a hαm hd hdm hmH hinm hz'd ha haB
    refine ⟨(h465 G M T L F φ c γ β hγ hγβ).2.2 (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator
        (hinm (commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαm hdm ha)) hz'γ), fun h => haB
      (mem_bzero_of_commutator_mem_bzero h464 h465 h466a c hq hα hαβ hαm hd hdm hmH hz'β hz'd
        ha h)⟩
  obtain ⟨hx₁γ, hx₁B⟩ := hx hαm₁ h₁ hd₁m₁ hne₁ (hin₁ m₁ hαm₁ hd₁m₁) hz'₁ hb₀ hb₀B
  obtain ⟨hx₂γ, hx₂B⟩ := hx hαn₀ h₂ hd₂n₀ hne₀ (hin₂ n₀ hαn₀ hd₂n₀) hz'₂ ha₀ ha₀B
  have h12 : ⁅b₀, z'⁆⁻¹ * ⁅a₀, z'⁆ ∈ bzero c α := hZβB (inv_mul_mem_zh_of_not_mem h465 c hq
    hγ hγβ hx₁γ hx₂γ (fun h => hx₁B (hZβB h)) (fun h => hx₂B (hZβB h)))
  obtain ⟨g, ⟨hgn, hgd⟩, hgα⟩ := exists_mem_qv_inf_ptQ h464 h465 h466a c hα hαn₀ hpt₂
  have hgs : g ∈ stab (puAmalgam c.pu.le) α := (mem_ptQ.mp hgd).1
  obtain ⟨h₃', hne31, hne32⟩ :=
    isPtOn_map_conj_ne h464 h465 h466a c hq hα hαβ hαn₀ h₁ h₂ n₁₂ hne₀ hgn hgd hgα
  have hd₃ : d₁.map (MulAut.conj g).toMonoidHom = d₃ := by
    rcases eq_of_isPtOn_three h464 h465 c hq hα hαβ h₁ h₂ h₃ h₃' n₁₂ n₁₃ n₂₃ with h | h | h
    · exact absurd h hne31
    · exact absurd h hne32
    · exact h
  obtain ⟨hαn₀', hd₂n₀', hn₀'H⟩ :=
    le_usup_smul_of_qv h464 c hα hαβ hz'β (hdH h₂) hd₂n₀ hne₀ hαn₀
  have hVn₀' : Vv (puAmalgam c.pu.le) (z' • n₀) =
      (Vv (puAmalgam c.pu.le) n₀).map (MulAut.conj z').toMonoidHom := vi_smul _ z' n₀ 2
  have ha₀' : z' * a₀ * z'⁻¹ ∈ ⁅Vv (puAmalgam c.pu.le) (z' • n₀), ptQ _ α d₂⁆ := by
    have hmap : (⁅Vv (puAmalgam c.pu.le) n₀, ptQ _ α d₂⁆ : Subgroup _).map
        (MulAut.conj z').toMonoidHom = ⁅Vv (puAmalgam c.pu.le) (z' • n₀), ptQ _ α d₂⁆ := by
      rw [Subgroup.map_commutator, ← hVn₀', map_conj_eq_of_mem_normalizer (hnQ hzs (hz'n h₂))]
    rw [← hmap]
    exact ⟨a₀, ha₀, rfl⟩
  have hBn : ∀ {t x : (puAmalgam c.pu.le).Universal}, t ∈ stab (puAmalgam c.pu.le) α →
      x ∉ bzero c α → t * x * t⁻¹ ∉ bzero c α := fun {t x} ht hxB h =>
    hxB ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c α ht) x).mpr h)
  have hgQ := hnQ hgs (mem_ptQ.mp hgd).2.1
  have hga₀ := conj_mem_commutator_of_mem_normalizer
    (ptQ_le_normalizer_vv h464 h465 h466a c hα hαn₀ hd₂n₀ hgd) hgQ ha₀
  have hga₀' := conj_mem_commutator_of_mem_normalizer
    (ptQ_le_normalizer_vv h464 h465 h466a c hα hαn₀' hd₂n₀' hgd) hgQ ha₀'
  have hp := inv_mul_mem_bzero_of_inactive h464 h465 h466a c hq hα hαβ hγ hγβ hαn₀ h₂ hd₂n₀ hne₀
    (hin₂ n₀ hαn₀ hd₂n₀) hz'γ hz'β hz'₂ ha₀ hga₀ ha₀B (hBn hgs ha₀B)
  have hr := inv_mul_mem_bzero_of_inactive h464 h465 h466a c hq hα hαβ hγ hγβ hαn₀' h₂ hd₂n₀'
    hn₀'H (hin₂ _ hαn₀' hd₂n₀') hz'γ hz'β hz'₂ ha₀' hga₀' (hBn hzs ha₀B)
    (hBn hgs (hBn hzs ha₀B))
  have ha₀'s : z' * a₀ * z'⁻¹ ∈ stab (puAmalgam c.pu.le) α := vv_le_stab_self c α
    (I466b.vv_le_vv_of_adj c.pu hα hαn₀'
      (commutator_vv_ptQ_le_vv h464 h465 h466a c hα hαn₀' hd₂n₀' ha₀'))
  have hx₂g : ⁅a₀, z'⁆⁻¹ * (g * ⁅a₀, z'⁆ * g⁻¹) ∈ bzero c α := by
    have e : ⁅a₀, z'⁆⁻¹ * (g * ⁅a₀, z'⁆ * g⁻¹) = (z' * a₀ * z'⁻¹) *
        ((a₀⁻¹ * (g * a₀ * g⁻¹)) * ((z' * a₀ * z'⁻¹)⁻¹ * (g * (z' * a₀ * z'⁻¹) * g⁻¹))⁻¹) *
        (z' * a₀ * z'⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c α ha₀'s) _).mp
      (Subgroup.mul_mem _ hp (Subgroup.inv_mem _ hr))
  have h21 : ⁅a₀, z'⁆⁻¹ * ⁅b₀, z'⁆ ∈ bzero c α := by
    have := Subgroup.inv_mem _ h12
    rwa [mul_inv_rev, inv_inv] at this
  have hx₁g : (g * ⁅b₀, z'⁆ * g⁻¹)⁻¹ * ⁅b₀, z'⁆ ∈ bzero c α := by
    have e : (g * ⁅b₀, z'⁆ * g⁻¹)⁻¹ * ⁅b₀, z'⁆ =
        (g * (⁅b₀, z'⁆⁻¹ * ⁅a₀, z'⁆) * g⁻¹) * (⁅a₀, z'⁆⁻¹ * (g * ⁅a₀, z'⁆ * g⁻¹))⁻¹ *
          (⁅a₀, z'⁆⁻¹ * ⁅b₀, z'⁆) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c α hgs) _).mp h12)
      (Subgroup.inv_mem _ hx₂g)) h21
  have hC₁ := commutator_mem_centralizer_pencil h464 h465 h466a c hq hα hαm₁ hd₁m₁ (hcard h₁)
    hb₀ hzs (hz'n h₁)
  have hC₂ := commutator_mem_centralizer_pencil h464 h465 h466a c hq hα hαn₀ hd₂n₀ (hcard h₂)
    ha₀ hzs (hz'n h₂)
  have hC₃ : g * ⁅b₀, z'⁆ * g⁻¹ ∈
      Subgroup.centralizer (pencil (puAmalgam c.pu.le) α d₃ : Set _) := by
    have h := conj_mem_centralizer_map hC₁ g
    rwa [← pencil_smul, MulAction.mem_stabilizer_iff.mp hgs, hd₃] at h
  have hZγV : ZM (puAmalgam c.pu.le) γ ≤ Vv _ α :=
    (zm_le_vv_of_adj hγβ.symm hγ).trans (I466b.vv_le_vv_of_adj c.pu hα hαβ)
  have hx₁V := hZγV hx₁γ
  have hx₂V := hZγV hx₂γ
  have hgx₁V : g * ⁅b₀, z'⁆ * g⁻¹ ∈ Vv (puAmalgam c.pu.le) α :=
    (Subgroup.mem_normalizer_iff.mp (hVs hgs) _).mp hx₁V
  apply hx₁B
  refine mem_bzero_of_three h464 h465 c hq hα hαβ h₁ h₂ h₃ n₁₂ n₁₃ n₂₃ hx₁V ?_
  intro P hP v hv
  have hvV : v ∈ Vv (puAmalgam c.pu.le) α := pencil_le_vv c hα P hv
  rcases hP with rfl | rfl | rfl
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hC₁ v hv).symm]
    exact Subgroup.one_mem _
  · have e : ⁅b₀, z'⁆ = ⁅a₀, z'⁆ * (⁅a₀, z'⁆⁻¹ * ⁅b₀, z'⁆) := by group
    rw [e]
    exact commutator_mul_bzero_mem_zloc c hx₂V h21 hvV
      (Subgroup.mem_centralizer_iff.mp hC₂ v hv).symm
  · have e : ⁅b₀, z'⁆ = (g * ⁅b₀, z'⁆ * g⁻¹) * ((g * ⁅b₀, z'⁆ * g⁻¹)⁻¹ * ⁅b₀, z'⁆) := by group
    rw [e]
    exact commutator_mul_bzero_mem_zloc c hgx₁V hx₁g hvV
      (Subgroup.mem_centralizer_iff.mp hC₃ v hv).symm

end CFSG.Quasithin.MS93.S46R
