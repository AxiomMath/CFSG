module

public import CFSG.Quasithin.MS93.S46R468C1
public import CFSG.Quasithin.MS93.S46R468LvA
public import CFSG.Quasithin.MS93.S46R468E

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem qv_le_ptQ (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : P ≤ ZM (puAmalgam c.pu.le) x) : Qv (puAmalgam c.pu.le) x ≤ ptQ _ x P := by
  intro t ht
  have htc : ∀ z ∈ ZM (puAmalgam c.pu.le) x, z * t = t * z := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hx hz) t ht).symm
  refine ⟨qv_le_stab _ x ht, Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun a ha => htc a (hP ha)), fun z hz => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (htc z hz)]
  exact Subgroup.one_mem _

theorem relIndex_qv_inf_ptQ (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x m P) :
    (Qv (puAmalgam c.pu.le) x).relIndex (Qv _ m ⊓ ptQ _ x P) = Fintype.card F := by
  have hPc := card_of_isPtOn h464 h465 c hx hxm hP
  have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPc]; exact Fintype.card_ne_zero)
  have hAs : Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P ≤ stab _ x :=
    inf_le_left.trans (qv_le_stab_of_adj _ hxm.symm)
  refine le_antisymm ?_ ?_
  · rw [← hPc]
    exact relIndex_qv_le_of_commutator_mem h464 h465 h466a c hx hxm inf_le_left
      fun a ha z hz => (mem_ptQ.mp ha.2).2.2 z hz
  · obtain ⟨ψ, hψs, hψU, hPco, hT⟩ := exists_coord_pt h464 h465 h466a c hx hxm hP
    have hQ := natImage_ptQ c hx hψs hψU (le_uloc_of_isPtOn c hx hP) hPco
    rw [← card_natImage_eq_relIndex c.pu c.via hx hψU hAs, ← Nat.card_eq_fintype_card,
      ← card_rootGroup (F := F) (show (0 : Fin 3) ≠ 2 by decide)]
    refine Subgroup.card_le_of_le fun A hA => ?_
    obtain ⟨t, ht, rfl⟩ := mem_natImage.mp (show A ∈ natImage ψ (Qv (puAmalgam c.pu.le) m) from
      hT ▸ Subgroup.mem_sup_left hA)
    obtain ⟨s, hs, hse⟩ := mem_natImage.mp (show toSL3 ψ t ∈ natImage ψ (ptQ _ x P) from
      hQ ▸ Subgroup.mem_sup_right hA)
    refine mem_natImage.mpr ⟨t, ⟨ht, ?_⟩, rfl⟩
    have h1 : toSL3 ψ (s⁻¹ * t) = 1 := by rw [map_mul, map_inv, hse, inv_mul_cancel]
    have h2 := (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψU _).mp h1
    have e : (t : (puAmalgam c.pu.le).Universal) = (s : (puAmalgam c.pu.le).Universal) *
        ((s⁻¹ * t : ↥(stab (puAmalgam c.pu.le) x)) : (puAmalgam c.pu.le).Universal) := by simp
    rw [e]
    exact Subgroup.mul_mem _ hs (qv_le_ptQ c hx ((le_uloc_of_isPtOn c hx hP).trans
      (uloc_le_zm c.pu (isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩) hx)) h2)

theorem relIndex_ptQ (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x m P) :
    (Qv (puAmalgam c.pu.le) x).relIndex (ptQ _ x P) = Fintype.card F ^ 2 := by
  obtain ⟨ψ, hψs, hψU, hPco, -⟩ := exists_coord_pt h464 h465 h466a c hx hxm hP
  rw [← card_natImage_eq_relIndex c.pu c.via hx hψU (fun t ht => (mem_ptQ.mp ht).1),
    natImage_ptQ c hx hψs hψU (le_uloc_of_isPtOn c hx hP) hPco, card_qPt,
    Nat.card_eq_fintype_card]

theorem isPtOn_of_le (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    (hPm : P ≤ Usup (puAmalgam c.pu.le) x m) : IsPtOn (puAmalgam c.pu.le) x m P := by
  have hPc := card_of_isPtOn h464 h465 c hx hxβ hP
  obtain ⟨β', hxβ', hne, hPe⟩ := hP
  by_cases hm : Usup (puAmalgam c.pu.le) x m = Usup _ x β
  · exact ⟨β', hxβ', hm ▸ hne, by rw [hm]; exact hPe⟩
  · refine ⟨β, hxβ, fun he => hm he.symm, ?_⟩
    have hc := card_usup_inf_usup h464 h465 c hx hxm hxβ hm
    have : Finite ↥(Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x β) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
    exact Subgroup.eq_of_le_of_card_ge (le_inf hPm (hPe ▸ inf_le_left)) (by rw [hc, hPc])

theorem relIndex_mul_le_relIndex_sup {𝔾 : Type*} [Group 𝔾] {Q A B : Subgroup 𝔾}
    (hQB : Q ≤ B) (hAB : A ⊓ B ≤ Q) (hfin : B.relIndex (A ⊔ B) ≠ 0) :
    Q.relIndex A * Q.relIndex B ≤ Q.relIndex (A ⊔ B) := by
  rw [← Subgroup.relIndex_mul_relIndex Q B (A ⊔ B) hQB le_sup_right, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  calc Q.relIndex A = B.relIndex A := by
        rw [← Subgroup.inf_relIndex_right Q A, ← Subgroup.inf_relIndex_right B A]
        congr 1
        exact le_antisymm (inf_le_inf_right _ hQB)
          (le_inf ((le_of_eq (inf_comm B A)).trans hAB) inf_le_right)
    _ ≤ B.relIndex (A ⊔ B) := Subgroup.relIndex_le_of_le_right le_sup_left hfin

theorem ptQ_le_sup_qv_inf (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ℓ m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x m) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPe : P = Usup (puAmalgam c.pu.le) x ℓ ⊓ Usup _ x m) :
    ptQ (puAmalgam c.pu.le) x P ≤
      (Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P) ⊔ (Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hPℓ : IsPtOn (puAmalgam c.pu.le) x ℓ P := ⟨m, hxm, Ne.symm hne, hPe⟩
  have hPm : IsPtOn (puAmalgam c.pu.le) x m P := ⟨ℓ, hxℓ, hne, by rw [hPe, inf_comm]⟩
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x :=
    (le_uloc_of_isPtOn c hx hPℓ).trans (uloc_le_zm c.pu hfull hx)
  have hQP := qv_le_ptQ c hx hPZ
  have hs : ptQ (puAmalgam c.pu.le) x P ≤ stab _ x := fun t ht => (mem_ptQ.mp ht).1
  set A := Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P with hAdef
  set B := Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P with hBdef
  have hQA : Qv (puAmalgam c.pu.le) x ≤ A := le_inf (qv_le_qv _ c.pu.hyp20 hx hxℓ) hQP
  have hQB : Qv (puAmalgam c.pu.le) x ≤ B := le_inf (qv_le_qv _ c.pu.hyp20 hx hxm) hQP
  have hABP : A ⊔ B ≤ ptQ (puAmalgam c.pu.le) x P := sup_le inf_le_right inf_le_right
  have hAB : A ⊓ B ≤ Qv (puAmalgam c.pu.le) x :=
    (inf_le_inf inf_le_left inf_le_left).trans (qv_inf_qv_le_qv h464 h465 h466a c hx hxℓ hxm hne)
  have hlow : Fintype.card F ^ 2 ≤ (Qv (puAmalgam c.pu.le) x).relIndex (A ⊔ B) := by
    have h1 := relIndex_mul_le_relIndex_sup hQB hAB
      (relIndex_ne_zero_of_le_stab c hx (hABP.trans hs) _)
    rwa [relIndex_qv_inf_ptQ h464 h465 h466a c hx hxℓ hPℓ,
      relIndex_qv_inf_ptQ h464 h465 h466a c hx hxm hPm, ← sq] at h1
  have hmul := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam c.pu.le) x) (A ⊔ B) (ptQ _ x P)
    (hQA.trans le_sup_left) hABP
  rw [relIndex_ptQ h464 h465 h466a c hx hxm hPm] at hmul
  have hpos : 0 < Fintype.card F ^ 2 := pow_pos Fintype.card_pos 2
  have hr1 : (A ⊔ B).relIndex (ptQ (puAmalgam c.pu.le) x P) ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Fintype.card F ^ 2 * (A ⊔ B).relIndex (ptQ (puAmalgam c.pu.le) x P)
        ≤ (Qv (puAmalgam c.pu.le) x).relIndex (A ⊔ B) *
          (A ⊔ B).relIndex (ptQ (puAmalgam c.pu.le) x P) := Nat.mul_le_mul_right _ hlow
      _ = Fintype.card F ^ 2 * 1 := by rw [hmul, mul_one]
  have hr0 := relIndex_ne_zero_of_le_stab c hx hs (A ⊔ B)
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem BadConf.exists_crit_pt (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α₀ α₀' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α₀ α₀')
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x ℓ P) :
    ∃ α'', BadConf c x α'' ∧ Usup (puAmalgam c.pu.le) x (geo _ x α'' 1) = Usup _ x ℓ ∧
      ZM (puAmalgam c.pu.le) α'' ≤ ptQ _ x P := by
  have hc := hB.crit
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α₀ (geo _ α₀ α₀' 1) := by
    have := adj_geo_crit c.b4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ hc.1 hαβ hx hxℓ
  have hB₁ := hB.smul g
  rw [hg1] at hB₁
  have hgeo : geo (puAmalgam c.pu.le) x (g • α₀') 1 = ℓ := by
    rw [← hg1, geo_smul, hg2]
  obtain ⟨p, hp, hZp⟩ := hB₁.exists_center h464 h465 h466a
  rw [hgeo] at hp hZp
  obtain ⟨k, hk, hkN, hkp⟩ := exists_conj_pt h464 h465 h466a c hx hxℓ hp hP
  have hkx : k • x = x := MulAction.mem_stabilizer_iff.mp hk
  have hB₂ := hB₁.smul k
  rw [hkx] at hB₂
  refine ⟨k • g • α₀', hB₂, ?_, ?_⟩
  · have e1 : geo (puAmalgam c.pu.le) x (k • g • α₀') 1 = k • ℓ := by
      rw [← hkx, geo_smul, hgeo]
    have e2 : Usup (puAmalgam c.pu.le) x (k • ℓ) =
        (Usup (puAmalgam c.pu.le) x ℓ).map (MulAut.conj k).toMonoidHom := by
      rw [← usup_smul, hkx]
    rw [e1, e2, Usup, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
      (stab_le_normalizer_of_smul _ (fun g' δ => zv_smul _ g' δ) x hk),
      map_conj_eq_of_mem_normalizer hkN]
  · have e3 : ptQ (puAmalgam c.pu.le) x (p.map (MulAut.conj k).toMonoidHom) =
        (ptQ (puAmalgam c.pu.le) x p).map (MulAut.conj k).toMonoidHom := by
      rw [← ptQ_smul, hkx]
    rw [zm_smul, ← hkp, e3]
    exact Subgroup.map_mono (hZp.trans inf_le_right)

theorem commutator_commutator_mem_zm_of_crit (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x α'' m : Vtx (puAmalgam c.pu.le)}
    (hc : IsCritical (puAmalgam c.pu.le) x α'') (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x (geo _ x α'' 1) ≠ Usup _ x m)
    (hZV : ZM (puAmalgam c.pu.le) α'' ≤
      Subgroup.normalizer (Vv (puAmalgam c.pu.le) m : Set (puAmalgam c.pu.le).Universal))
    {w z₁ z₂ : (puAmalgam c.pu.le).Universal} (hw : w ∈ Vv (puAmalgam c.pu.le) m)
    (hz₁ : z₁ ∈ ZM (puAmalgam c.pu.le) α'') (hz₂ : z₂ ∈ ZM (puAmalgam c.pu.le) α'') :
    ⁅⁅w, z₁⁆, z₂⁆ ∈ ZM (puAmalgam c.pu.le) x := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hx := hc.1
  set ℓ := geo (puAmalgam c.pu.le) x α'' 1 with hℓdef
  set γ := geo (puAmalgam c.pu.le) x α'' 2 with hγdef
  set β := geo (puAmalgam c.pu.le) x α'' 3 with hβdef
  have hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hℓγ : (puAmalgam c.pu.le).treeGraph.Adj ℓ γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β := adj_geo_crit hb4 hc (i := 2) (by omega)
  have hβα : (puAmalgam c.pu.le).treeGraph.Adj β α'' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [show (3 : ℕ) + 1 = 4 from rfl, geo_four hb4 hc] at this
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := isMVtx_geo_two' hb4 hc
  have hα'' : IsMVtx (puAmalgam c.pu.le) α'' := hc.isMVtx_right _ c.pu.hyp20
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hmℓ : m ≠ ℓ := fun he => hne (by rw [he])
  have hVT : Vv (puAmalgam c.pu.le) m ≤ Qv _ ℓ :=
    vv_le_qv_of_dist_le_two hb4 hm (dist_eq_two_of_adj_adj _ hxm.symm hxℓ hmℓ).le
  have hVγ : Vv (puAmalgam c.pu.le) m ≤ stab _ γ := hVT.trans (qv_le_stab_of_adj _ hℓγ)
  have hZγ : ZM (puAmalgam c.pu.le) α'' ≤ Qv _ γ := zm_le_qv_of_dist_lt _ hα'' (by
    rw [tdist_comm, dist_geo_crit_right hb4 hc (by omega)]; omega)
  have hQγβ : Qv (puAmalgam c.pu.le) γ ≤ Qv _ β := qv_le_qv _ c.pu.hyp20 hγ hγβ
  have hUZ : Usup (puAmalgam c.pu.le) α'' β ≤ ZM _ α'' := I464.usup_le_zm c.pu hα'' hβα.symm
  have hUZγ : Usup (puAmalgam c.pu.le) α'' β ≤ ZM _ γ :=
    (h464' α'' β hα'' hβα.symm).trans (zh_le_zm _ hγβ)
  have hcomQ : ∀ {a : (puAmalgam c.pu.le).Universal}, a ∈ Qv (puAmalgam c.pu.le) γ →
      ∀ {z : (puAmalgam c.pu.le).Universal}, z ∈ ZM (puAmalgam c.pu.le) α'' →
        ⁅a, z⁆ ∈ Usup (puAmalgam c.pu.le) α'' β := fun {a} ha {z} hz => by
    rw [Usup, zv_of_isMVtx _ hα'', ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hz (hQγβ ha))
  have hZab : ∀ {a b : (puAmalgam c.pu.le).Universal}, a ∈ ZM (puAmalgam c.pu.le) α'' →
      b ∈ ZM (puAmalgam c.pu.le) α'' → a * b = b * a := fun {a b} ha hb' =>
    Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hα'' hb')
      a (zm_le_qv_self _ hα'' c.pu.critDist_pos ha)
  have hnV : ∀ {z : (puAmalgam c.pu.le).Universal}, z ∈ ZM (puAmalgam c.pu.le) α'' →
      ∀ {v : (puAmalgam c.pu.le).Universal}, v ∈ Vv (puAmalgam c.pu.le) m →
        ⁅v, z⁆ ∈ Vv (puAmalgam c.pu.le) m := fun {z} hz {v} hv => by
    have e : ⁅v, z⁆ = v * (z * v⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hv ((Subgroup.mem_normalizer_iff.mp (hZV hz) _).mp
      (Subgroup.inv_mem _ hv))
  set a := ⁅w, z₁⁆ with hadef
  have haV : a ∈ Vv (puAmalgam c.pu.le) m := hnV hz₁ hw
  have haQ : a ∈ Qv (puAmalgam c.pu.le) γ := by
    have e : a = (w * z₁ * w⁻¹) * z₁⁻¹ := by rw [hadef, commutatorElement_def]
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_qv _ γ (hVγ hw)) _).mp (hZγ hz₁)) (Subgroup.inv_mem _ (hZγ hz₁))
  by_cases hVQ : Vv (puAmalgam c.pu.le) m ≤ Qv _ γ
  · have haZ : a ∈ ZM (puAmalgam c.pu.le) α'' := hUZ (hcomQ (hVQ hw) hz₁)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZab haZ hz₂)]
    exact Subgroup.one_mem _
  · have hy1 : ⁅a, z₂⁆ ∈ Vv (puAmalgam c.pu.le) m := hnV hz₂ haV
    have hy2 : ⁅a, z₂⁆ ∈ ZM (puAmalgam c.pu.le) γ := hUZγ (hcomQ haQ hz₂)
    refine zh_le_zm _ hxℓ (by_contra fun hyℓ => hVQ fun t ht => ?_)
    exact mem_qv_of_commute c.pu c.via h464' hsq h466 hγ hℓγ.symm hy2 hyℓ (hVT ht)
      (vv_comm c.pu hb hm ht hy1)

theorem BadConf.commutator_commutator_mem_zm (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α₀ α₀' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α₀ α₀')
    {x m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x m P) {v t₁ t₂ : (puAmalgam c.pu.le).Universal}
    (hv : v ∈ Vv (puAmalgam c.pu.le) m) (ht₁ : t₁ ∈ ptQ (puAmalgam c.pu.le) x P)
    (ht₂ : t₂ ∈ ptQ (puAmalgam c.pu.le) x P) : ⁅⁅v, t₁⁆, t₂⁆ ∈ ZM (puAmalgam c.pu.le) x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hPm : P ≤ Usup (puAmalgam c.pu.le) x m := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  obtain ⟨ℓ, hxℓ, hneℓ, hPe⟩ := hP
  have hPℓ : IsPtOn (puAmalgam c.pu.le) x ℓ P := ⟨m, hxm, Ne.symm hneℓ, by rw [hPe, inf_comm]⟩
  obtain ⟨α'', hB'', hU'', hZQ⟩ := hB.exists_crit_pt h464 h465 h466a hx hxℓ hPℓ
  have hc'' := hB''.crit
  have hx1 : (puAmalgam c.pu.le).treeGraph.Adj x (geo _ x α'' 1) := by
    have := adj_geo_crit c.b4 hc'' (i := 0) (by omega)
    rwa [geo_zero] at this
  have hTeq : Qv (puAmalgam c.pu.le) (geo _ x α'' 1) = Qv _ ℓ :=
    qv_eq_of_usup_eq h464 h465 h466a c hx hx1 hxℓ hU''
  have hZT : ZM (puAmalgam c.pu.le) α'' ≤ Qv _ ℓ := by
    rw [← hTeq]
    exact zm_le_qv_of_dist_lt _ (hc''.isMVtx_right _ c.pu.hyp20) (by
      rw [tdist_comm, dist_geo_crit_right c.b4 hc'' (by omega)]
      have := c.b4
      omega)
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x :=
    (le_uloc_of_isPtOn c hx hPℓ).trans (uloc_le_zm c.pu hfull hx)
  have hQP := qv_le_ptQ c hx hPZ
  have hZs : ZM (puAmalgam c.pu.le) α'' ≤ stab _ x := hZQ.trans fun t ht => (mem_ptQ.mp ht).1
  have hZQn : ZM (puAmalgam c.pu.le) α'' ≤ Subgroup.normalizer (Qv (puAmalgam c.pu.le) x : Set _) :=
    hZs.trans (stab_le_normalizer_qv _ x)
  have hidx : (Qv (puAmalgam c.pu.le) x).relIndex (ZM _ α'' ⊔ Qv _ x) = Fintype.card F := by
    rw [S46.relIndex_sup_of_le_normalizer hZQn]
    exact hB''.relIndex_qv_zm h464 h465 h466a
  have hsub : ZM (puAmalgam c.pu.le) α'' ⊔ Qv _ x ≤ Qv _ ℓ ⊓ ptQ _ x P :=
    sup_le (le_inf hZT hZQ) (le_inf (qv_le_qv _ c.pu.hyp20 hx hxℓ) hQP)
  have hroot : Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P ≤ ZM _ α'' ⊔ Qv _ x := by
    have hmul := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam c.pu.le) x) (ZM _ α'' ⊔ Qv _ x)
      (Qv _ ℓ ⊓ ptQ _ x P) le_sup_right hsub
    rw [hidx, relIndex_qv_inf_ptQ h464 h465 h466a c hx hxℓ hPℓ] at hmul
    have hq : 0 < Fintype.card F := Fintype.card_pos
    have h1 : (ZM (puAmalgam c.pu.le) α'' ⊔ Qv _ x).relIndex (Qv _ ℓ ⊓ ptQ _ x P) = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hq (hmul.trans (mul_one _).symm)
      exact this
    exact Subgroup.relIndex_eq_one.mp h1
  have hTm : Qv (puAmalgam c.pu.le) x ≤ Qv _ m := qv_le_qv _ c.pu.hyp20 hx hxm
  have hQP' : ptQ (puAmalgam c.pu.le) x P ≤ ZM _ α'' ⊔ Qv _ m := by
    refine (ptQ_le_sup_qv_inf h464 h465 h466a c hx hxℓ hxm hneℓ
      (by rw [hPe, inf_comm])).trans
      (sup_le (hroot.trans (sup_le le_sup_left (hTm.trans le_sup_right)))
        (inf_le_left.trans le_sup_right))
  have hZn : ZM (puAmalgam c.pu.le) α'' ≤ Subgroup.normalizer (Qv (puAmalgam c.pu.le) m : Set _) :=
    hZQ.trans (ptQ_le_normalizer_qv h464 h465 h466a c hx hxm hPm)
  have hZnV : ZM (puAmalgam c.pu.le) α'' ≤ Subgroup.normalizer (Vv (puAmalgam c.pu.le) m : Set _) :=
    hZQ.trans (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm hPm)
  have hdec : ∀ {t}, t ∈ ptQ (puAmalgam c.pu.le) x P →
      ∃ z ∈ ZM (puAmalgam c.pu.le) α'', ∃ s ∈ Qv (puAmalgam c.pu.le) m, z * s = t := by
    intro t ht
    have h1 : t ∈ ((ZM (puAmalgam c.pu.le) α'' ⊔ Qv _ m : Subgroup _) : Set _) := hQP' ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZn] at h1
    obtain ⟨z, hz, s, hs, he⟩ := h1
    exact ⟨z, hz, s, hs, he⟩
  have hZxn : stab (puAmalgam c.pu.le) x ≤ Subgroup.normalizer (ZM (puAmalgam c.pu.le) x : Set _) :=
    stab_le_normalizer_zm _ x
  have hVm : Vv (puAmalgam c.pu.le) m ≤ stab _ x :=
    (vv_le_qv_of_dist_le_two c.b4 hm (by rw [SimpleGraph.dist_self]; omega)).trans
      (qv_le_stab_of_adj _ hxm.symm)
  have hTs : Qv (puAmalgam c.pu.le) m ≤ stab _ x := qv_le_stab_of_adj _ hxm.symm
  have hVTm : ∀ {w s}, w ∈ Vv (puAmalgam c.pu.le) m → s ∈ Qv (puAmalgam c.pu.le) m →
      ⁅w, s⁆ ∈ ZM (puAmalgam c.pu.le) x := fun hw hs =>
    zh_le_zm _ hxm (commutator_vv_qv_le_zh c.pu h464' hm (Subgroup.commutator_mem_commutator hw hs))
  have hnV : ∀ {z w}, z ∈ ZM (puAmalgam c.pu.le) α'' → w ∈ Vv (puAmalgam c.pu.le) m →
      ⁅w, z⁆ ∈ Vv (puAmalgam c.pu.le) m := fun {z w} hz hw => by
    have e : ⁅w, z⁆ = w * (z * w⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hw ((Subgroup.mem_normalizer_iff.mp (hZnV hz) _).mp
      (Subgroup.inv_mem _ hw))
  have hne1 : Usup (puAmalgam c.pu.le) x (geo _ x α'' 1) ≠ Usup _ x m := by
    rw [hU'']
    exact hneℓ
  obtain ⟨z₁, hz₁, s₁, hs₁, rfl⟩ := hdec ht₁
  obtain ⟨z₂, hz₂, s₂, hs₂, rfl⟩ := hdec ht₂
  have e1 : ⁅v, z₁ * s₁⁆ = ⁅v, z₁⁆ * (z₁ * ⁅v, s₁⁆ * z₁⁻¹) := by
    simp only [commutatorElement_def]; group
  set y := ⁅v, z₁⁆ with hydef
  set ζ := z₁ * ⁅v, s₁⁆ * z₁⁻¹ with hζdef
  have hyV : y ∈ Vv (puAmalgam c.pu.le) m := hnV hz₁ hv
  have hζ : ζ ∈ ZM (puAmalgam c.pu.le) x :=
    (Subgroup.mem_normalizer_iff.mp (hZxn (hZs hz₁)) _).mp (hVTm hv hs₁)
  rw [e1]
  have e2 : ⁅y * ζ, z₂ * s₂⁆ = y * ⁅ζ, z₂ * s₂⁆ * y⁻¹ * ⁅y, z₂ * s₂⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  have hζt : ⁅ζ, z₂ * s₂⁆ ∈ ZM (puAmalgam c.pu.le) x := hPZ ((mem_ptQ.mp ht₂).2.2 ζ hζ)
  have e3 : ⁅y, z₂ * s₂⁆ = ⁅y, z₂⁆ * (z₂ * ⁅y, s₂⁆ * z₂⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e3]
  refine Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hZxn (hVm hyV)) _).mp hζt)
    (Subgroup.mul_mem _ (commutator_commutator_mem_zm_of_crit h464 h465 h466a c hc'' hxm hne1
      hZnV hv hz₁ hz₂) ((Subgroup.mem_normalizer_iff.mp (hZxn (hZs hz₂)) _).mp (hVTm hyV hs₂)))

theorem BadConf.commutator_vv_ptQ_le_ptSub (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α₀ α₀' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α₀ α₀')
    {x m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x m P) :
    ⁅Vv (puAmalgam c.pu.le) m, ptQ _ x P⁆ ≤ ptSub (puAmalgam c.pu.le) x P := by
  have hPm : P ≤ Usup (puAmalgam c.pu.le) x m := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  rw [Subgroup.commutator_le]
  intro v hv t ht
  refine Subgroup.subset_closure ⟨m, hxm, hPm, ?_, fun t' ht' =>
    hB.commutator_commutator_mem_zm h464 h465 h466a hx hxm hP hv ht ht'⟩
  have e : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ hv ((Subgroup.mem_normalizer_iff.mp
    (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm hPm ht) _).mp (Subgroup.inv_mem _ hv))

theorem BadConf.commutator_pencil_ptQ_le_ptSub (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α₀ α₀' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α₀ α₀')
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) :
    ⁅pencil (puAmalgam c.pu.le) x P, ptQ _ x P⁆ ≤ ptSub (puAmalgam c.pu.le) x P := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x :=
    (le_uloc_of_isPtOn c hx hP).trans (uloc_le_zm c.pu hfull hx)
  have hpen : pencil (puAmalgam c.pu.le) x P = ⨆ m, ⨆ (_ : (puAmalgam c.pu.le).treeGraph.Adj x m ∧
      P ≤ Usup (puAmalgam c.pu.le) x m), Vv (puAmalgam c.pu.le) m :=
    le_antisymm (pencil_le fun m hm hP' => le_iSup₂_of_le m ⟨hm, hP'⟩ le_rfl)
      (iSup₂_le fun m h => vv_le_pencil h.1 h.2)
  rw [hpen]
  refine I467.commutator_biSup_le_of (fun m hm => ?_) (fun m hm => ?_)
  · exact hB.commutator_vv_ptQ_le_ptSub h464 h465 h466a hx hm.1
      (isPtOn_of_le h464 h465 c hx hxβ hm.1 hP hm.2)
  · refine le_normalizer_ptSub ((I466b.vv_le_vv_of_adj c.pu hx hm.1).trans (vv_le_stab_self c x))
      fun v hv => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun a ha => (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hx
          (hPZ ha)) v (vv_le_qv c.pu hb hx (I466b.vv_le_vv_of_adj c.pu hx hm.1 hv))).symm)

end CFSG.Quasithin.MS93.S46R
