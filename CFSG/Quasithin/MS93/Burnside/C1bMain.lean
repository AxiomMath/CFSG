module

public import CFSG.Quasithin.MS93.Burnside.C1bSec
public import CFSG.Quasithin.MS93.S45Cen
public import CFSG.Quasithin.MS93.S45Q4PD
public import CFSG.Quasithin.MS93.S45UA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support.S45CircA
public import CFSG.Quasithin.MS93.S45Phi1

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Local

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideC1b_commutator_vhat_qv_le (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h12 : 12 ≤ a) (haN : a + 12 ≤ N) :
    ⁅Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)), Qv (puAmalgam c.hyp.le) (p a)⁆ ≤
      ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p (a + 2)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (p (a + 1)) (p (a + 2)) := hp.adj (a + 1) (by omega)
  have hQβ : Qv (puAmalgam h.le) (p a) ≤ Qv _ (p (a + 1)) := qv_le_qv _ h20 hα hαβ
  have hQγ : Qv (puAmalgam h.le) (p a) ≤ stab _ (p (a + 2)) :=
    hQβ.trans (qv_le_stab_of_adj _ hβγ)
  refine le_inf ?_ ?_
  · exact (Subgroup.commutator_mono (c.vhat_le_whv_self (δ := p a)) le_rfl).trans
      (c.commutator_whv_qv_le' hZV hp ha h12 haN)
  · obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h c.via hγ
    have hVcγ : ⁅Vcirc h.le L (p (a + 2)), Qv (puAmalgam h.le) (p a)⁆ ≤ Vcirc h.le L (p (a + 2)) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hQγ.trans (c.stab_le_normalizer_vcirc _))
    have hZγ : ⁅ZM (puAmalgam h.le) (p (a + 2)), Qv (puAmalgam h.le) (p a)⁆ ≤
        Vcirc h.le L (p (a + 2)) := by
      refine ((c.commutator_zm_qv_le_usup_inf_zloc hα hγ hαβ hβγ.symm).trans inf_le_left).trans ?_
      rw [c.usup_eq_uloc_inf_centralizer hψγ hγ hβγ.symm]
      exact inf_le_left.trans (uloc_le_vcirc c hγ)
    have hVcs : Vcirc h.le L (p (a + 2)) ≤ stab (puAmalgam h.le) (p (a + 2)) :=
      (c.vcirc_le_vv _).trans ((c.vv_le_qv' hγ).trans (qv_le_stab _ _))
    have hZs : ZM (puAmalgam h.le) (p (a + 2)) ≤ stab (puAmalgam h.le) (p (a + 2)) :=
      (zm_le_qv_self _ hγ h.critDist_pos).trans (qv_le_stab _ _)
    exact S46.commutator_sup_le_of_le_normalizer (c.stab_le_normalizer_vcirc _) hVcs hZs hVcγ hZγ

theorem burnsideC1b_commutator_qv_whv_le_of_rig (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h12 : 12 ≤ a) (haN : a + 12 ≤ N)
    (hR : ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p (a + 2)) ≤ Vcirc c.hyp.le L (p a)) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), whv c.hyp (p a) (p (a + 2))⁆ ≤ Vcirc c.hyp.le L (p a) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  have hle := (burnsideC1b_commutator_vhat_qv_le c hZV hp ha h12 haN).trans hR
  have hKQ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_qv _ _
  have hKV : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vcirc h.le L (p a) : Set _) :=
    c.stab_le_normalizer_vcirc _
  have hVhK : Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)) ≤ stab (puAmalgam h.le) (p a) :=
    (c.vhat_le_vv hγ).trans ((vi_le_qv _ (by rw [tdist_comm, hd2, c.b8]; omega)).trans
      (qv_le_stab _ _))
  rw [Subgroup.commutator_comm]
  refine commutator_conjCl_le hKV hVhK fun g hg => ?_
  have e : ⁅(Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))).map (MulAut.conj g).toMonoidHom,
      Qv (puAmalgam h.le) (p a)⁆ =
      (⁅Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)), Qv (puAmalgam h.le) (p a)⁆).map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hKQ hg)]
  rw [e]
  exact (Subgroup.map_mono hle).trans (map_conj_eq_of_mem_normalizer (hKV hg)).le

theorem burnsideC1b_commutator_inf_zm_le_vcirc_of_pair (c : Ctx M T L φ) (h14 : MS14AS)
    (hSQ : SQTKQuot) (hZV : c.HZV) (hq : 4 ≤ Fintype.card F)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hpair : ⁅Qv (puAmalgam c.hyp.le) (p a), whv c.hyp (p a) (p (a + 2))⁆ ≤
      Vcirc c.hyp.le L (p a)) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ ZM _ (p a) ≤
      Vcirc c.hyp.le L (p a) := by
  classical
  have h := c.hyp
  have h20 := h.hyp20
  haveI hchar : CharP F 2 := c.charP
  have hQ4 := S45Q4.hQ4 c
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) (by omega)
  set K := stab (puAmalgam h.le) (p a) with hK
  set Q := Qv (puAmalgam h.le) (p a) with hQ
  set Lt := Ltil h.le L (p a) with hLt
  set V := ⁅Q, Lt⁆ with hV
  set Vc := Vcirc h.le L (p a) with hVc
  set Z := ZM (puAmalgam h.le) (p a) with hZ
  set Vh := Vc ⊔ Z with hVh
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set X₁ := conjCl K (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔ Wh with hX₁
  set X₂ := conjCl K (Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔ Wh with hX₂
  set Y₁ := ⁅X₁, K⁆ ⊔ Wh with hY₁
  set Y₂ := ⁅X₂, K⁆ ⊔ Wh with hY₂
  set Xs := Y₁ ⊔ Y₂ with hXs
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα hαβ
  have hQK : Q ≤ K := qv_le_stab _ _
  have hLK : Lt ≤ K := ltil_le_stab h _
  have hKQ : K ≤ Subgroup.normalizer (Q : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_qv _ _
  have hKL : K ≤ Subgroup.normalizer (Lt : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_ltil h _
  have hKK : K ≤ Subgroup.normalizer (K : Set (puAmalgam h.le).Universal) := Subgroup.le_normalizer
  have hKV : K ≤ Subgroup.normalizer (V : Set (puAmalgam h.le).Universal) :=
    MS93.le_normalizer_commutator hKQ hKL
  have hKVc : K ≤ Subgroup.normalizer (Vc : Set (puAmalgam h.le).Universal) :=
    c.stab_le_normalizer_vcirc _
  have hKZ : K ≤ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_zm _ _
  have hKVh : K ≤ Subgroup.normalizer (Vh : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup hKVc hKZ
  have hKWh : K ≤ Subgroup.normalizer (Wh : Set (puAmalgam h.le).Universal) :=
    S4A.le_normalizer_conjCl _ _
  have hKX₁ : K ≤ Subgroup.normalizer (X₁ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh
  have hKX₂ : K ≤ Subgroup.normalizer (X₂ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh
  have hKY₁ : K ≤ Subgroup.normalizer (Y₁ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (MS93.le_normalizer_commutator hKX₁ hKK) hKWh
  have hKY₂ : K ≤ Subgroup.normalizer (Y₂ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (MS93.le_normalizer_commutator hKX₂ hKK) hKWh
  have hKXs : K ≤ Subgroup.normalizer (Xs : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup hKY₁ hKY₂
  have hX₁₂Q : X₁ ⊔ X₂ ≤ Q := c.top_le_qv hp hp' ha (by omega) hpp'
  have hX₁Q : X₁ ≤ Q := le_sup_left.trans hX₁₂Q
  have hX₂Q : X₂ ≤ Q := le_sup_right.trans hX₁₂Q
  have hWhQ : Wh ≤ Q := (le_sup_right : Wh ≤ X₁).trans hX₁Q
  have hY₁X₁ : Y₁ ≤ X₁ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX₁) le_sup_right
  have hY₂X₂ : Y₂ ≤ X₂ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX₂) le_sup_right
  have hXsQ : Xs ≤ Q := sup_le (hY₁X₁.trans hX₁Q) (hY₂X₂.trans hX₂Q)
  have hXsK : Xs ≤ K := hXsQ.trans hQK
  have hWhK : Wh ≤ K := hWhQ.trans hQK
  have hWhXs : Wh ≤ Xs := (le_sup_right : Wh ≤ Y₁).trans le_sup_left
  have hVcVh : Vc ≤ Vh := le_sup_left
  have hZVh : Z ≤ Vh := le_sup_right
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hVcQ : Vc ≤ Q := (c.vcirc_le_vv _).trans (c.vv_le_qv' hα)
  have hVQ : V ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLK.trans hKQ)
  have hVWh : V ⊔ Wh = Xs := c.sup_whv_eq hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hVXs : V ≤ Xs := hVWh ▸ le_sup_left
  have hψker : ∀ g : ↥K, ψ g = 1 ↔ (g : (puAmalgam h.le).Universal) ∈ Q := by
    intro g
    rw [← toSL3_eq_one_iff', ← MonoidHom.mem_ker, c.ker_toSL3_eq hα hψ, Subgroup.mem_subgroupOf]
  have hQWhV : ∀ x ∈ Q, ∀ w ∈ Wh, ⁅x, w⁆ ∈ Vc := fun x hx w hw =>
    hpair (Subgroup.commutator_mem_commutator hx hw)
  have hWhQV : ∀ w ∈ Wh, ∀ x ∈ Q, ⁅w, x⁆ ∈ Vc := fun w hw x hx => by
    have h1 : ⁅w, x⁆ ∈ ⁅Wh, Q⁆ := Subgroup.commutator_mem_commutator hw hx
    rw [Subgroup.commutator_comm] at h1
    exact hpair h1
  have hX₁W : ⁅X₁, Q⁆ ≤ Wh := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  have hX₂W : ⁅X₂, Q⁆ ≤ Wh := by
    have := c.commutator_top_qv_le hZV hQ4 hp' ha h34 (by omega)
    rw [hpa, hpa2] at this
    exact this
  have hXsQW : ∀ x ∈ Xs, ∀ q ∈ Q, ⁅x, q⁆ ∈ Wh := by
    have h1 : ⁅X₁ ⊔ X₂, Q⁆ ≤ Wh :=
      S46.commutator_sup_le_of_le_normalizer hKWh (hX₁Q.trans hQK) (hX₂Q.trans hQK) hX₁W hX₂W
    intro x hx q hq
    exact h1 (Subgroup.commutator_mem_commutator (sup_le_sup hY₁X₁ hY₂X₂ hx) hq)
  have hmid : IsSumOfNaturalModulesVia K Wh Vh ψ true 2 :=
    c.isSum_whv h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hψs hψ hT
  have hVV₁ : ∀ x ∈ Wh, ∀ y ∈ Wh, x * y * x⁻¹ * y⁻¹ ∈ Vc := by
    intro x hx y hy
    rw [← commutatorElement_def]
    exact hWhQV x hx y (hWhQ hy)
  have hsqWh : ∀ x ∈ Wh, x * x ∈ Vc := by
    have hWhn : Wh ≤ Subgroup.normalizer (Vc : Set (puAmalgam h.le).Universal) := hWhK.trans hKVc
    have hWW : ⁅Wh, Wh⁆ ≤ Vc := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact hWhQV x hx y (hWhQ hy)
    have hle : Wh ≤ sqSub' Wh Vc hWW hWhn := by
      show conjCl K (Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) ≤ _
      refine iSup₂_le fun g hg => ?_
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · exact le_iSup₂_of_le (f := fun g (_ : g ∈ K) =>
          (Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))).map (MulAut.conj g).toMonoidHom) g hg
          le_rfl ⟨v, hv, rfl⟩
      · have hv2 : v ^ 2 = 1 := c.sq_eq_one_of_mem_vhat hZV hp (a := a + 2) (ha.add even_two)
          (by omega) (by omega) hv
        rw [← map_pow, hv2, map_one]
        exact Vc.one_mem
    intro x hx
    have := (hle hx).2
    rwa [sq] at this
  have hKVh' : ∀ g ∈ K, ∀ z ∈ Vh, g * z * g⁻¹ * z⁻¹ ∈ Vc := by
    intro g hg z hz
    have hn : Vc ≤ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal) :=
      (hVcQ.trans hQK).trans hKZ
    have hz' : z ∈ ((Vc ⊔ Z : Subgroup _) : Set (puAmalgam h.le).Universal) := hz
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Vc Z hn] at hz'
    obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_mul.mp hz'
    have h1 : g * w * g⁻¹ * w⁻¹ ∈ Vc :=
      ((uloc_sup_hloc_le c hα).trans inf_le_left) (commutator_zm_mem c hα hg hw)
    have h2 : g * v * g⁻¹ ∈ Vc := (Subgroup.mem_normalizer_iff.mp (hKVc hg) v).mp hv
    have e : g * (v * w) * g⁻¹ * (v * w)⁻¹ = (g * v * g⁻¹) * (g * w * g⁻¹ * w⁻¹) * v⁻¹ := by
      group
    rw [e]
    exact Vc.mul_mem (Vc.mul_mem h2 h1) (Vc.inv_mem hv)
  have hker₁ : ∀ g : ↥K, ψ g = 1 → ∀ v ∈ Wh,
      (g : (puAmalgam h.le).Universal) * v * (g : (puAmalgam h.le).Universal)⁻¹ * v⁻¹ ∈ Vc := by
    intro g hg v hv
    rw [← commutatorElement_def]
    exact hQWhV _ ((hψker g).mp hg) v hv
  obtain ⟨Mm, hVcM, hMWh, hKM, hMVh, hMsup⟩ := burnsideC1b_exists_complement_sec hq hψs hmid
    hWhK hVcVh hKVc (fun g hg => (hψker g).mpr (hVcQ hg)) hVV₁ hsqWh hKVh' hker₁
  have hMQ : Mm ≤ Q := hMWh.trans hWhQ
  have hKWhM : ∀ g ∈ K, ∀ w ∈ Wh, g * w * g⁻¹ * w⁻¹ ∈ Mm := by
    intro g hg w hw
    have hn : Mm ≤ Subgroup.normalizer (Vh : Set (puAmalgam h.le).Universal) :=
      (hMQ.trans hQK).trans hKVh
    have hw' : w ∈ ((Mm ⊔ Vh : Subgroup _) : Set (puAmalgam h.le).Universal) := by
      rw [hMsup]; exact hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Mm Vh hn] at hw'
    obtain ⟨m, hm, v, hv, rfl⟩ := Set.mem_mul.mp hw'
    have h1 : g * v * g⁻¹ * v⁻¹ ∈ Mm := hVcM (hKVh' g hg v hv)
    have h2 : g * m * g⁻¹ ∈ Mm := (Subgroup.mem_normalizer_iff.mp (hKM hg) m).mp hm
    have e : g * (m * v) * g⁻¹ * (m * v)⁻¹ = (g * m * g⁻¹) * (g * v * g⁻¹ * v⁻¹) * m⁻¹ := by
      group
    rw [e]
    exact Mm.mul_mem (Mm.mul_mem h2 h1) (Mm.inv_mem hm)
  obtain ⟨hY12, htop₁, htop₂⟩ :=
    c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have htop : IsSumOfNaturalModulesVia K Xs Wh ψ false 2 :=
    S46.isSumOfNaturalModulesVia_two htop₁ htop₂ hKXs (hXsK.trans hKY₁) (hXsK.trans hKY₂) hY12 rfl
  have hpairY : ∀ (Yi Yj : Subgroup (puAmalgam h.le).Universal),
      IsSumOfNaturalModulesVia K Yi Wh ψ false 1 → IsSumOfNaturalModulesVia K Yj Wh ψ false 1 →
      Yi ≤ Xs → Yj ≤ Xs → ∀ x ∈ Yi, ∀ v ∈ Yj, ⁅x, v⁆ ∈ Mm := by
    intro Yi Yj hi hj hiX hjX
    exact burnsideC1b_commutator_mem_sec hψs hi hj (hiX.trans hXsK) (hjX.trans hXsK) hMWh hMWh
      hKM (fun g hg => (hψker g).mpr (hMQ hg)) hWhK
      (fun x hx v hv => hXsQW x (hiX hx) v (hXsQ (hjX hv))) hKWhM
      (fun z hz v hv => hVcM (hWhQV z hz v (hXsQ (hjX hv))))
      (fun x hx z hz => hVcM (hQWhV x (hXsQ (hiX hx)) z hz))
  have hY1 : Y₁ ≤ Xs := le_sup_left
  have hY2 : Y₂ ≤ Xs := le_sup_right
  have hXsXs : ⁅Xs, Xs⁆ ≤ Mm := by
    have hc : ∀ Yi : Subgroup (puAmalgam h.le).Universal,
        IsSumOfNaturalModulesVia K Yi Wh ψ false 1 → Yi ≤ Xs → ⁅Yi, Xs⁆ ≤ Mm := by
      intro Yi hi hiX
      rw [Subgroup.commutator_comm]
      refine S46.commutator_sup_le_of_le_normalizer hKM (hY1.trans hXsK) (hY2.trans hXsK) ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx v hv
        exact hpairY Y₁ Yi htop₁ hi hY1 hiX x hx v hv
      · rw [Subgroup.commutator_le]
        intro x hx v hv
        exact hpairY Y₂ Yi htop₂ hi hY2 hiX x hx v hv
    exact S46.commutator_sup_le_of_le_normalizer hKM (hY1.trans hXsK) (hY2.trans hXsK)
      (hc Y₁ htop₁ hY1) (hc Y₂ htop₂ hY2)
  have hLtp : ⁅Lt, Lt⁆ = Lt := S4A.ltil_perfect h hα
  have hVn : K ≤ Subgroup.normalizer ((⁅V, Lt⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    MS93.le_normalizer_commutator hKV hKL
  have hVLt : ⁅V, Lt⁆ = V := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLK.trans hKV)) ?_
    exact S46.commutator_le_of_perfect hLtp le_rfl le_rfl (hLK.trans hVn) (hQK.trans hVn)
  have hcommVLt : ∀ v ∈ V, ∀ l ∈ Lt, ⁅v, l⁆ ∈ V := fun v hv l hl => by
    rw [← hVLt]; exact Subgroup.commutator_mem_commutator hv hl
  have hXsn : Xs ≤ Subgroup.normalizer (Mm : Set (puAmalgam h.le).Universal) := hXsK.trans hKM
  have hsqXs : ∀ x ∈ Xs, x * x ∈ Mm := by
    have hle : Xs ≤ sqSub' Xs Mm hXsXs hXsn := by
      refine hVWh.ge.trans (sup_le ?_ ?_)
      · rw [← hVLt, Subgroup.commutator_le]
        intro v hv l hl
        refine ⟨hVXs (hcommVLt v hv l hl), ?_⟩
        have huV : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hKV (hLK hl)) v).mp hv
        have hv2 : v * v ∈ Wh := burnsideC1b_mul_self_mem_of_isSum htop (hVXs hv)
        have hm₀ : l * (v * v)⁻¹ * l⁻¹ * (v * v)⁻¹⁻¹ ∈ Mm :=
          hKWhM l (hLK hl) _ (Wh.inv_mem hv2)
        have hc : ⁅l * v * l⁻¹, v⁻¹⁆ ∈ Mm :=
          hXsXs (Subgroup.commutator_mem_commutator (hVXs huV) (Xs.inv_mem (hVXs hv)))
        have hvK : v * v ∈ K := K.mul_mem (hQK (hVQ hv)) (hQK (hVQ hv))
        have huK : l * v * l⁻¹ ∈ K := hQK (hVQ huV)
        have e : ⁅v, l⁆ ^ 2 =
            ((v * v) * (l * (v * v)⁻¹ * l⁻¹ * (v * v)⁻¹⁻¹) * (v * v)⁻¹) *
              ((l * v * l⁻¹) * ⁅l * v * l⁻¹, v⁻¹⁆ * (l * v * l⁻¹)⁻¹) := by
          simp only [commutatorElement_def, sq]
          group
        rw [e]
        exact Mm.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKM hvK) _).mp hm₀)
          ((Subgroup.mem_normalizer_iff.mp (hKM huK) _).mp hc)
      · intro w hw
        refine ⟨hWhXs hw, ?_⟩
        rw [sq]
        exact hVcM (hsqWh w hw)
    intro x hx
    have := (hle hx).2
    rwa [sq] at this
  have hθ : Xs ≤ commIn Xs Q Mm hXsn := by
    refine hVWh.ge.trans (sup_le ?_ ?_)
    · rw [← hVLt, Subgroup.commutator_le]
      intro v hv l hl
      refine mem_commIn.mpr ⟨hVXs (hcommVLt v hv l hl), fun q hq => ?_⟩
      have hyXs : ⁅v, l⁆ ∈ Xs := hVXs (hcommVLt v hv l hl)
      have hlql : l⁻¹ * q * l ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hKQ (hLK (Lt.inv_mem hl))) q).mp hq
        simpa using this
      have haW : ⁅v, q⁆ ∈ Wh := hXsQW v (hVXs hv) q hq
      have hbW : ⁅v, l⁻¹ * q * l⁆ ∈ Wh := hXsQW v (hVXs hv) _ hlql
      have hq' : q⁻¹ * l⁻¹ * q * l ∈ V := by
        have := Subgroup.commutator_mem_commutator (Q.inv_mem hq) (Lt.inv_mem hl)
        rw [commutatorElement_def, inv_inv, inv_inv] at this
        exact this
      have hn₁ : ⁅v, q⁆⁻¹ * ⁅v, l⁻¹ * q * l⁆ ∈ Mm := by
        have e : ⁅v, q⁆⁻¹ * ⁅v, l⁻¹ * q * l⁆ = q * ⁅v, q⁻¹ * l⁻¹ * q * l⁆ * q⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hKM (hQK hq)) _).mp
          (hXsXs (Subgroup.commutator_mem_commutator (hVXs hv) (hVXs hq')))
      have hn₂ : l * ⁅v, l⁻¹ * q * l⁆ * l⁻¹ * ⁅v, l⁻¹ * q * l⁆⁻¹ ∈ Mm :=
        hKWhM l (hLK hl) _ hbW
      have hc₃ : ⁅v, l⁆ * ⁅v, q⁆⁻¹ * ⁅v, l⁆⁻¹ * ⁅v, q⁆ ∈ Mm := by
        have := hVcM (hQWhV _ (hXsQ hyXs) _ (Wh.inv_mem haW))
        rw [commutatorElement_def, inv_inv] at this
        exact this
      have hyK : ⁅v, l⁆ ∈ K := hXsK hyXs
      have haK : ⁅v, q⁆ ∈ K := hWhK haW
      have e : ⁅⁅v, l⁆, q⁆ =
          (⁅v, l⁆ * (⁅v, q⁆⁻¹ * ⁅v, l⁻¹ * q * l⁆)⁻¹ * ⁅v, l⁆⁻¹) *
            (⁅v, l⁆ * ⁅v, q⁆⁻¹ * ⁅v, l⁆⁻¹ * ⁅v, q⁆) *
            (⁅v, q⁆⁻¹ * (⁅v, l⁆ * (l * ⁅v, l⁻¹ * q * l⁆ * l⁻¹ * ⁅v, l⁻¹ * q * l⁆⁻¹)⁻¹ *
              ⁅v, l⁆⁻¹) * ⁅v, q⁆⁻¹⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine Mm.mul_mem (Mm.mul_mem ?_ hc₃) ?_
      · exact (Subgroup.mem_normalizer_iff.mp (hKM hyK) _).mp (Mm.inv_mem hn₁)
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hKM hyK) _).mp (Mm.inv_mem hn₂)
        exact (Subgroup.mem_normalizer_iff.mp (hKM (K.inv_mem haK)) _).mp h1
    · intro w hw
      exact mem_commIn.mpr ⟨hWhXs hw, fun q hq => hVcM (hWhQV w hw q hq)⟩
  have hkerTop : ∀ g : ↥K, ψ g = 1 → ∀ v ∈ Xs,
      (g : (puAmalgam h.le).Universal) * v * (g : (puAmalgam h.le).Universal)⁻¹ * v⁻¹ ∈ Mm := by
    intro g hg v hv
    have h1 := (mem_commIn.mp (hθ hv)).2 _ ((hψker g).mp hg)
    have e : (g : (puAmalgam h.le).Universal) * v * (g : (puAmalgam h.le).Universal)⁻¹ * v⁻¹ =
        ⁅v, (g : (puAmalgam h.le).Universal)⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Mm.inv_mem h1
  obtain ⟨X, hMX, hXXs, hKX, hXWh, hXsup⟩ := burnsideC1b_exists_complement_sec hq hψs htop hXsK
    hMWh hKM (fun g hg => (hψker g).mpr (hMQ hg))
    (fun x hx y hy => by
      rw [← commutatorElement_def]
      exact hXsXs (Subgroup.commutator_mem_commutator hx hy))
    hsqXs hKWhM hkerTop
  have hXsLt : ⁅Xs, Lt⁆ ≤ X := by
    rw [← hXsup]
    refine S46.commutator_sup_le_of_le_normalizer hKX (hXXs.trans hXsK) hWhK ?_ ?_
    · exact (Subgroup.commutator_mono le_rfl hLK).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX)
    · rw [Subgroup.commutator_le]
      intro w hw l hl
      have h1 := hKWhM l (hLK hl) w⁻¹ (Wh.inv_mem hw)
      have e : ⁅w, l⁆ = w * (l * w⁻¹ * l⁻¹ * w⁻¹⁻¹) * w⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hMX ((Subgroup.mem_normalizer_iff.mp (hKM (hWhK hw)) _).mp h1)
  have hVX : V ≤ X := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    exact S45.commutator_mem_of_perfect hLtp hXXs (hXsXs.trans hMX) hXsLt
      (fun l' hl' => hVXs (Subgroup.commutator_mem_commutator hq hl')) hl
  intro x hx
  obtain ⟨hxV, hxZ⟩ := Subgroup.mem_inf.mp hx
  have hxM : x ∈ Mm := by
    rw [← hXWh]
    exact Subgroup.mem_inf.mpr ⟨hVX hxV, hVhWh (hZVh hxZ)⟩
  have hxVc : x ∈ Mm ⊓ Vh := Subgroup.mem_inf.mpr ⟨hxM, hZVh hxZ⟩
  rw [hMVh] at hxVc
  exact hxVc

end Local

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
