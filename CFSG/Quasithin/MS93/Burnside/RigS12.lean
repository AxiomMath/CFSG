module

public import CFSG.Quasithin.MS93.Burnside.RigAbs
public import CFSG.Quasithin.MS93.S45Q4PD
public import CFSG.Quasithin.MS93.S45X0

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

@[expose] def burnsideRig_IndexBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Ctx M T L φ), c.HZV → 4 ≤ Fintype.card F →
    ∀ (p : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N →
    ∀ a : ℕ, Even a → 34 ≤ a → a + 30 ≤ N →
    ∀ X : Subgroup (puAmalgam c.hyp.le).Universal, X ≤ whv c.hyp (p a) (p (a + 2)) →
      (∀ x ∈ X, ∀ t ∈ Qv (puAmalgam c.hyp.le) (p (a + 1)),
        ⁅x, t⁆ ∈ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) →
      Nat.card ↥X ≤ Fintype.card F ^ 2 * Nat.card ↥(Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))

section Local

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideRig_qv_le_qv_sup_qv (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h24 : 24 ≤ a) (haN : a + 12 ≤ N) :
    Qv (puAmalgam c.hyp.le) (p (a + 1)) ≤ Qv _ (p a) ⊔ Qv _ (p (a + 2)) := by
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have h1 := c.qv_le_whv_sup_qv_right hZV hp ha2 (by omega) (by omega)
  rw [show a - 2 + 3 = a + 1 by omega, show a - 2 + 2 = a by omega,
    show a - 2 + 4 = a + 2 by omega] at h1
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hd : (puAmalgam c.hyp.le).treeGraph.dist (p (a - 2)) (p a) = 2 := by
    rw [hp.dist_eq' (i := a - 2) (j := a) (by omega) (by omega)]; omega
  have hW : whv c.hyp (p (a - 2)) (p a) ≤ Qv (puAmalgam c.hyp.le) (p a) :=
    c.whv_le_qv_of_dist hα hd (by rw [hd]; omega)
  exact h1.trans (sup_le_sup_right hW _)

theorem burnsideRig_commutator_le_of_le_sup {𝔾 : Type} [Group 𝔾] {A X Qa Qg Tb : Subgroup 𝔾}
    (hT : Tb ≤ Qa ⊔ Qg) (hQa : Qa ≤ Subgroup.normalizer (X : Set 𝔾))
    (hQg : Qg ≤ Subgroup.normalizer (X : Set 𝔾)) (ha : ⁅A, Qa⁆ ≤ X) (hg : ⁅A, Qg⁆ ≤ X) :
    ⁅A, Tb⁆ ≤ X := by
  rw [Subgroup.commutator_comm]
  refine (Subgroup.commutator_mono hT le_rfl).trans ?_
  refine commutator_sup_left_le hQa hQg ?_ ?_
  · rw [Subgroup.commutator_comm]; exact ha
  · rw [Subgroup.commutator_comm]; exact hg

theorem burnsideRig_card_vhat_inf_le (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    Nat.card ↥((Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ⊓
        (Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)))) ≤
      Nat.card ↥(ZM (puAmalgam c.hyp.le) (p a)) * Nat.card F := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  have hTs : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab _ (p a) := qv_le_stab_of_adj _ hαβ.symm
  have hQγT : Qv (puAmalgam h.le) (p (a + 2)) ≤ Qv _ (p (a + 1)) := qv_le_qv _ h20 hγ hγβ
  have hQαs : Qv (puAmalgam h.le) (p a) ≤ stab _ (p a) := qv_le_stab _ _
  have hKZ := stab_le_normalizer_zm (puAmalgam h.le) (p a)
  set I := (Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a)) ⊓
    (Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) with hI
  have hIa : ⁅I, Qv (puAmalgam h.le) (p a)⁆ ≤ ZM _ (p a) :=
    (Subgroup.commutator_mono (inf_le_left.trans (c.vhat_le_vv hα)) le_rfl).trans
      ((c.commutator_vv_qv_le_zloc hα).trans (zloc_le_zm h c.full hα))
  have hIg : ⁅I, Qv (puAmalgam h.le) (p (a + 2))⁆ ≤ ZM _ (p a) := by
    obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h c.via hγ
    have hZβ : Zloc h.le L (p (a + 2)) ≤ ZH (puAmalgam h.le) (p (a + 1)) := by
      rw [c.zh_eq_usup_sup_zloc hψγ hγ hγβ]; exact le_sup_right
    exact (Subgroup.commutator_mono (inf_le_right.trans (c.vhat_le_vv hγ)) le_rfl).trans
      ((c.commutator_vv_qv_le_zloc hγ).trans (hZβ.trans (zh_le_zm _ hαβ)))
  have hIT : ⁅I, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ ZM _ (p a) :=
    burnsideRig_commutator_le_of_le_sup (burnsideRig_qv_le_qv_sup_qv c hZV hp ha (by omega)
      (by omega)) (hQαs.trans hKZ) ((hQγT.trans hTs).trans hKZ) hIa hIg
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
  have hx : Even x := (Nat.even_add.mp ha).mpr (by decide)
  have hdt := c.dual_eq_true hp hx (by omega) (by omega) hψs hψ (c.isSum_bloc hα hd)
  subst hdt
  set Nn := NatSec.ofIsSum hd with hNn
  set S : Set (Fin 3 → F) :=
    {y | ∀ g ∈ natImage ψ (Qv (puAmalgam h.le) (p (x + 6 + 1))), dualMat g *ᵥ y = y} with hS
  have hS2 : 2 ≤ Module.finrank F ↥(commN (natImage ψ (Qv (puAmalgam h.le) (p (x + 6 + 1))))) := by
    have hfc := c.fixN_eq_commN_qv hψ hα hαβ
    rw [← hfc.1, hfc.2]
  have hScard : Nat.card S ≤ Nat.card F := S45U.card_dualFix_le' hS2 S fun y hy => hy
  have hSI : ∀ v ∈ I, Nn.coord v ∈ S := by
    intro v hv
    exact S45U.dualFix_of_comm Nn hTs (Subgroup.mem_inf.mp hv).1
      (fun t ht => hIT (Subgroup.commutator_mem_commutator hv ht))
  have : Finite ↥(stab (puAmalgam h.le) (p (x + 6))) := S4A.finite_stab h hα
  have : Finite ↥(ZM (puAmalgam h.le) (p (x + 6))) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _)))
  have : Finite S := Set.toFinite S
  calc Nat.card ↥I ≤ Nat.card ↥(ZM (puAmalgam h.le) (p (x + 6))) * Nat.card S :=
        burnsideRig_card_le_of_coord Nn inf_le_left hSI
    _ ≤ _ := Nat.mul_le_mul_left _ hScard

theorem burnsideRig_le_card_vhat_sup (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    Fintype.card F ^ 2 * Nat.card ↥(Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ≤
      Nat.card ↥((Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  set Vα := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVα
  set Vγ := Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2)) with hVγ
  have hVγs : Vγ ≤ stab (puAmalgam h.le) (p a) :=
    (c.vhat_le_vv hγ).trans ((vi_le_qv _ (by rw [tdist_comm, hd2, c.b8]; omega)).trans
      (qv_le_stab _ _))
  have hKVα : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vα : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hprod := burnsideRig_card_sup_mul_card_inf (hVγs.trans hKVα)
  obtain ⟨ψγ, hψγs, hψγ⟩ := exists_natural_Uloc h c.via hγ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hγ hψγs hψγ
  have hcγ := burnsideRig_card_eq_of_natSec (NatSec.ofIsSum hd)
  have hZ : Nat.card ↥(ZM (puAmalgam h.le) (p (a + 2))) = Nat.card ↥(ZM (puAmalgam h.le) (p a)) := by
    have h1 := Subgroup.relIndex_mul_card (H := ZH (puAmalgam h.le) (p (a + 1)))
      (K := ZM _ (p a))
    rw [inf_of_le_left (zh_le_zm _ hαβ), c.relIndex_zh hα hαβ] at h1
    have h2 := Subgroup.relIndex_mul_card (H := ZH (puAmalgam h.le) (p (a + 1)))
      (K := ZM _ (p (a + 2)))
    rw [inf_of_le_left (zh_le_zm _ hγβ), c.relIndex_zh hγ hγβ] at h2
    rw [← h1, ← h2]
  have h1 := burnsideRig_card_vhat_inf_le c hZV hp ha h34 haN
  rw [← hVα, ← hVγ] at h1
  rw [hcγ, hZ] at hprod
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hZpos : 0 < Nat.card ↥(ZM (puAmalgam h.le) (p a)) := by
    have : Finite ↥(stab (puAmalgam h.le) (p a)) := S4A.finite_stab h hα
    have : Finite ↥(ZM (puAmalgam h.le) (p a)) :=
      Finite.of_injective _ (Subgroup.inclusion_injective
        ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _)))
    exact Nat.card_pos
  rw [Nat.card_eq_fintype_card (α := F)] at h1 hprod
  set z := Nat.card ↥(ZM (puAmalgam h.le) (p a))
  set q := Fintype.card F
  have key : Nat.card ↥(Vγ ⊔ Vα) * (z * q) ≥ q ^ 2 * Nat.card ↥Vα * (z * q) := by
    calc Nat.card ↥(Vγ ⊔ Vα) * (z * q) ≥ Nat.card ↥(Vγ ⊔ Vα) * Nat.card ↥(Vα ⊓ Vγ) :=
          Nat.mul_le_mul_left _ h1
      _ = z * q ^ 3 * Nat.card ↥Vα := hprod
      _ = q ^ 2 * Nat.card ↥Vα * (z * q) := by ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hZpos hq)

theorem burnsideRig_conj_mem_vhat_sup (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hb : ∀ X : Subgroup (puAmalgam c.hyp.le).Universal, X ≤ whv c.hyp (p a) (p (a + 2)) →
      (∀ x ∈ X, ∀ t ∈ Qv (puAmalgam c.hyp.le) (p (a + 1)),
        ⁅x, t⁆ ∈ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) →
      Nat.card ↥X ≤ Fintype.card F ^ 2 * Nat.card ↥(Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)))
    {g : (puAmalgam c.hyp.le).Universal} (hg : g ∈ stab (puAmalgam c.hyp.le) (p a))
    (hgT : g ∈ Subgroup.normalizer (Qv (puAmalgam c.hyp.le) (p (a + 1)) :
      Set (puAmalgam c.hyp.le).Universal))
    {x : (puAmalgam c.hyp.le).Universal}
    (hx : x ∈ (Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) ⊔
      (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) :
    g * x * g⁻¹ ∈ (Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) ⊔
      (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  set Vα := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVα
  set Vγ := Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2)) with hVγ
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set Tb := Qv (puAmalgam h.le) (p (a + 1)) with hTb
  have hK : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vα : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hKW : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hWs : Wh ≤ stab (puAmalgam h.le) (p a) :=
    (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans (qv_le_stab _ _)
  have hTs : Tb ≤ stab (puAmalgam h.le) (p a) := qv_le_stab_of_adj _ hαβ.symm
  set P := commIn Wh Tb Vα (hWs.trans hK) with hP
  have hVγW : Vγ ≤ Wh := c.vhat_le_whv_self
  have hVαW : Vα ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hVγP : Vγ ≤ P := by
    intro v hv
    refine mem_commIn.mpr ⟨hVγW hv, fun t ht => ?_⟩
    have h1 := c.commutator_vhat_qv_le_left hZV hp ha (by omega) (by omega)
      (Subgroup.commutator_mem_commutator hv ht)
    have hZγ : ZM (puAmalgam h.le) (p (a + 2)) ≤ Vα :=
      c.zm_le_vhat_right hZV hp ha (by omega) (by omega)
    exact (sup_le (le_sup_right : ZM (puAmalgam h.le) (p a) ≤ Vα) hZγ) h1
  have hVαP : Vα ≤ P := by
    intro v hv
    refine mem_commIn.mpr ⟨hVαW hv, fun t ht => ?_⟩
    rw [commutatorElement_def, show v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) by group]
    exact Vα.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hK (hTs ht)) _).mp (Vα.inv_mem hv))
  have hle : Vγ ⊔ Vα ≤ P := sup_le hVγP hVαP
  have : Finite ↥(stab (puAmalgam h.le) (p a)) := S4A.finite_stab h hα
  have hPW : P ≤ Wh := fun w hw => (mem_commIn.mp hw).1
  have : Finite ↥P := Finite.of_injective _ (Subgroup.inclusion_injective (hPW.trans hWs))
  have hPc := hb P hPW (fun w hw t ht => (mem_commIn.mp hw).2 t ht)
  have hge := burnsideRig_le_card_vhat_sup c hZV hp ha h34 haN
  have heq : Vγ ⊔ Vα = P := Subgroup.eq_of_le_of_card_ge hle (hPc.trans hge)
  rw [heq] at hx ⊢
  obtain ⟨hxW, hxc⟩ := mem_commIn.mp hx
  refine mem_commIn.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hKW hg) x).mp hxW, fun t ht => ?_⟩
  have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ Tb := (Subgroup.mem_normalizer_iff.mp (inv_mem hgT) t).mp ht
  rw [inv_inv] at ht'
  have h1 := hxc _ ht'
  have e : ⁅g * x * g⁻¹, t⁆ = g * ⁅x, g⁻¹ * t * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hK hg) _).mp h1

end Local

theorem burnsideRig_indexBound (h14 : MS14AS) (hSQ : SQTKQuot) : burnsideRig_IndexBound := by
  intro G _ _ M T L F _ _ φ c hZV hq p N hp a ha h34 haN X hXW hX
  have h := c.hyp
  have hQ4 := S45Q4.hQ4 c
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα hαβ
  have hW := c.isSum_whv h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hψs hψ hT
  have hTs : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab _ (p a) := qv_le_stab_of_adj _ hαβ.symm
  have hS2 : 2 ≤ Module.finrank F ↥(commN (natImage ψ (Qv (puAmalgam h.le) (p (a + 1))))) := by
    have hfc := c.fixN_eq_commN_qv hψ hα hαβ
    rw [← hfc.1, hfc.2]
  have : Finite ↥(stab (puAmalgam h.le) (p a)) := S4A.finite_stab h hα
  have : Finite ↥(Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (sup_le ((c.vcirc_le_vv _).trans ((c.vv_le_qv' hα).trans (qv_le_stab _ _)))
        ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _))))
  have h1 := burnsideRig_card_le_of_isSum_two hW hXW hTs hS2 hX
  rw [Nat.card_eq_fintype_card (α := F), mul_comm] at h1
  exact h1

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
