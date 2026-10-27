module

public import CFSG.Quasithin.MS93.Burnside.RigS35

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Local

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideRig_zm_inf_vcirc_le_vcirc_of_bound (c : Ctx M T L φ) (hZV : c.HZV)
    (hq : 4 ≤ Fintype.card F) {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hb : ∀ X : Subgroup (puAmalgam c.hyp.le).Universal, X ≤ whv c.hyp (p a) (p (a + 2)) →
      (∀ x ∈ X, ∀ t ∈ Qv (puAmalgam c.hyp.le) (p (a + 1)),
        ⁅x, t⁆ ∈ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) →
      Nat.card ↥X ≤ Fintype.card F ^ 2 * Nat.card ↥(Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) :
    ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p (a + 2)) ≤ Vcirc c.hyp.le L (p a) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  set St := ⁅(Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2))) ⊔
    (Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a)), Qv (puAmalgam h.le) (p a)⁆ with hSt
  have hStS : St ≤ ZM (puAmalgam h.le) (p a) ⊓ Vcirc h.le L (p (a + 2)) :=
    burnsideRig_commutator_le_zm_inf_vcirc c hZV hp ha h34 haN
  have hStZ : St ≤ ZM (puAmalgam h.le) (p a) := hStS.trans inf_le_left
  have hcapS := burnsideRig_inf_zh_le c hq hp ha h34 haN
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα hαβ
  have hinv : ∀ g ∈ stab (puAmalgam h.le) (p a), g ∈ Subgroup.normalizer
      (Qv (puAmalgam h.le) (p (a + 1)) : Set (puAmalgam h.le).Universal) →
        ∀ s ∈ St, g * s * g⁻¹ ∈ St := by
    intro g hg hgT s hs
    exact ML3.conj_mem_commutator
      (fun x hx => burnsideRig_conj_mem_vhat_sup c hZV hp ha h34 haN hb hg hgT hx)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ _ hg) y).mp hy) hs
  have hne : ¬ St ≤ ZH (puAmalgam h.le) (p (a + 1)) := fun hle =>
    burnsideRig_not_commutator_le_zh c hZV hp ha h34 haN
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans hle)
  have hsup := burnsideRig_exists_inv_mul_mem c hα hαβ hψs hψ hT hStZ hinv hne
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    classical
    by_contra hcon
    push Not at hcon
    have hle : Fintype.card F ≤ 2 := by
      have : (Finset.univ : Finset F) ⊆ {0, 1} := fun y _ => by
        by_cases hy : y = 0
        · simp [hy]
        · simp [hcon y hy]
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card this
        _ ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨e, he, heT⟩ := burnsideRig_exists_torus c hα hαβ hψs hψ hT l hl0
  have hsurj := burnsideRig_exists_inv_mul_mem_of_torus c hα hαβ hψ hT hl1 he
  have hZab : ∀ x ∈ ZM (puAmalgam h.le) (p a), ∀ y ∈ ZM (puAmalgam h.le) (p a),
      x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα hx) y
      (zm_le_qv_self _ hα h.critDist_pos hy)).symm
  have heB : (e : (puAmalgam h.le).Universal) ∈
      Subgroup.normalizer (ZH (puAmalgam h.le) (p (a + 1)) : Set (puAmalgam h.le).Universal) :=
    normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv _ heT
  have hStle : St ≤ ZM (puAmalgam h.le) (p a) ⊓ Vcirc h.le L (p a) :=
    burnsideRig_le_of_torus (A := ZM (puAmalgam h.le) (p a)) (B := ZH (puAmalgam h.le) (p (a + 1)))
      (e := (e : (puAmalgam h.le).Universal)) hZab (zh_le_zm _ hαβ)
      (fun z hz => (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ _ e.2) z).mp hz)
      (fun z hz => (Subgroup.mem_normalizer_iff.mp heB z).mp hz)
      (hinv _ e.2 heT)
      (fun z hz => by
        have h1 := (uloc_sup_hloc_le c hα) (commutator_zm_mem c hα e.2 hz)
        exact ⟨h1.2, h1.1⟩)
      hsurj (fun s hs => hcapS ⟨hStS hs.1, hs.2⟩)
      (fun z hz => by
        obtain ⟨s, hs, hsz⟩ := hsup z hz
        exact ⟨s, hs, s⁻¹ * z, hsz, by group⟩)
      hStZ
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hsup x hx.1
  have hsS := hStS hs
  have h1 : s⁻¹ * x ∈ ZM (puAmalgam h.le) (p a) ⊓ Vcirc h.le L (p (a + 2)) ⊓
      ZH (puAmalgam h.le) (p (a + 1)) :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hsS) hx, hsx⟩
  have e1 : x = s * (s⁻¹ * x) := by group
  rw [e1]
  exact Subgroup.mul_mem _ (hStle hs).2 (hcapS h1).2

theorem burnsideRig_zm_inf_vcirc_le_vcirc (h14 : MS14AS) (hSQ : SQTKQuot) (c : Ctx M T L φ)
    (hZV : c.HZV) (hq : 4 ≤ Fintype.card F) {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p (a + 2)) ≤ Vcirc c.hyp.le L (p a) :=
  burnsideRig_zm_inf_vcirc_le_vcirc_of_bound c hZV hq hp ha h34 haN
    (burnsideRig_indexBound h14 hSQ G M T L F φ c hZV hq p N hp a ha h34 haN)

end Local

theorem burnsideRig_s45C1bQ4 (h14 : MS14AS) (hSQ : SQTKQuot) : S45C1bQ4 := by
  intro G _ _ M T L F _ _ φ c hZV hq p N hp a ha h34 haN _
  exact burnsideC1b_commutator_inf_zm_le_vcirc_of_pair c h14 hSQ hZV hq hp ha h34 haN
    (burnsideC1b_commutator_qv_whv_le_of_rig c hZV hp ha (by omega) (by omega)
      (burnsideRig_zm_inf_vcirc_le_vcirc h14 hSQ c hZV hq hp ha h34 haN))

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
