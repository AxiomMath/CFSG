module

public import CFSG.Quasithin.MS93.S46I469Loc
public import CFSG.Quasithin.MS93.S46I469Crit

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464 CFSG.Quasithin.MS93.S46.I466b
open scoped commutatorElement

section B0

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
  (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

omit [Fintype F] in
include h463 in
theorem commute_commutator_vv (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {a b c : 𝔘} (ha : a ∈ Vv (puAmalgam h.le) α)
    (hb' : b ∈ Vv (puAmalgam h.le) α) (hc : c ∈ Vv (puAmalgam h.le) α) :
    c * ⁅a, b⁆ = ⁅a, b⁆ * c := by
  have hZ : ⁅a, b⁆ ∈ ZM 𝔛 α := h463 α hα (Subgroup.commutator_mem_commutator ha hb')
  exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hα hZ) c
    (vv_le_qv h hb hα hc))

omit [Fintype F] in
theorem commute_zm_vv (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {z w : 𝔘} (hz : z ∈ ZM (puAmalgam h.le) α)
    (hw : w ∈ Vv (puAmalgam h.le) α) : z * w = w * z :=
  (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hα hz) w
    (vv_le_qv h hb hα hw)).symm

omit [Fintype F] in
theorem commute_of_mem_stabCenter {α : Vtx (puAmalgam h.le)} {z g : 𝔘}
    (hz : z ∈ stabCenter (puAmalgam h.le) α) (hg : g ∈ stab (puAmalgam h.le) α) :
    g * z = z * g := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)

include hφ in
theorem mem_zloc_of_mem_stabCenter {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {z : 𝔘}
    (hz : z ∈ ZM (puAmalgam h.le) α) (hzc : z ∈ stabCenter (puAmalgam h.le) α) :
    z ∈ Zloc h.le L α :=
  zm_inf_centralizer_le_zloc h hφ hα ⟨hz, Subgroup.mem_centralizer_iff.mpr fun _ hg =>
    commute_of_mem_stabCenter h hzc hg⟩

omit [Fintype F] in
theorem zloc_le_stabCenter' (hfull : IsSL3Full M T L) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) : Zloc h.le L α ≤ stabCenter (puAmalgam h.le) α := by
  intro z hz
  have hzs : z ∈ stab 𝔛 α := puTrans_le_stab h.le _ α hz
  refine ⟨⟨z, hzs⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hz) g g.2

omit [Fintype F] in
theorem commute_zh {β : Vtx (puAmalgam h.le)} {a b : 𝔘} (ha : a ∈ ZH (puAmalgam h.le) β)
    (hb : b ∈ ZH (puAmalgam h.le) β) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β hb) a (zh_le_qv _ β ha))

include hφ h464 hsq h466 in
theorem usup_le_range_sup_zloc (hb : 2 < critDist (puAmalgam h.le))
    {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hγ : IsMVtx _ γ)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβγ : (puAmalgam h.le).treeGraph.Adj β γ)
    {x : 𝔘} (hx : x ∈ ZM (puAmalgam h.le) γ)
    (hc : ∀ w ∈ Vv (puAmalgam h.le) α, ∀ w' ∈ Vv (puAmalgam h.le) α, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w)
    (hnot : ¬ (commHomOf (Vv (puAmalgam h.le) α) x hc).range ≤ Zloc h.le L α)
    (hinv : ∀ g : 𝔘, IsOddL1 (puAmalgam h.le) α β g → ∀ y ∈ (commHomOf (Vv _ α) x hc).range,
      g * y * g⁻¹ ∈ (commHomOf (Vv (puAmalgam h.le) α) x hc).range ⊔ Zloc h.le L α) :
    Usup (puAmalgam h.le) α β ≤ (commHomOf (Vv (puAmalgam h.le) α) x hc).range ⊔ Zloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  set R := (commHomOf (Vv 𝔛 α) x hc).range with hRdef
  have hRZ : R ≤ ZH 𝔛 β := by
    rintro _ ⟨w, rfl⟩
    have hw : (w : 𝔘) ∈ Qv 𝔛 β := qv_le_qv _ h.hyp20 hα hαβ (vv_le_qv h hb hα w.2)
    have := h464 γ β hγ hβγ.symm
    rw [Usup, zv_of_isMVtx _ hγ] at this
    exact this (Subgroup.commutator_mem_commutator hx hw)
  have hZlZ : Zloc h.le L α ≤ ZH 𝔛 β := zloc_le_zh h hfull hα hαβ
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  set X := (R ⊔ Zloc h.le L α) ⊓ Uloc h.le L α with hXdef
  have hXU : X ≤ Usup 𝔛 α β := fun u hu => mem_usup_of_commute h hφ h464 hsq hα hαβ hu.2
    fun t ht => (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β
      ((sup_le hRZ hZlZ) hu.1)) t ht)
  have hXinv : ∀ g : 𝔘, IsOddL1 𝔛 α β g → ∀ y ∈ X, g * y * g⁻¹ ∈ X := by
    intro g hg y hy
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hUn hg.1) y).mp hy.2⟩
    have hle : (R ⊔ Zloc h.le L α).map (MulAut.conj g).toMonoidHom ≤ R ⊔ Zloc h.le L α := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨r, hr, rfl⟩
        exact hinv g hg r hr
      · rintro _ ⟨z, hz, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hz) g hg.1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [this, mul_inv_cancel_right]
        exact Subgroup.mem_sup_right hz
    exact hle ⟨y, hy.1, rfl⟩
  rcases eq_bot_or_eq_usup h hφ h464 hsq h466 hα hαβ hXU hXinv with hX | hX
  · exfalso
    apply hnot
    intro r hr
    obtain ⟨u, hu, ζ, hζ, hre⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb' => commute_zh h (h464 α β hα hαβ ha) (hZlZ hb'))
      (show r ∈ Usup 𝔛 α β ⊔ Zloc h.le L α by
        rw [← zh_eq_usup_sup_zloc h hφ h464 hsq hα hαβ]; exact hRZ hr)
    have huX : u ∈ X := by
      refine ⟨?_, usup_le_uloc' h hfull hα hαβ hu⟩
      have e : u = r * ζ⁻¹ := by rw [hre, mul_inv_cancel_right]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hζ))
    rw [hX, Subgroup.mem_bot] at huX
    rw [hre, huX, one_mul]
    exact hζ
  · rw [← hX]
    exact inf_le_left

include hφ h464 hsq h466 in
theorem range_eq_usup (hb : 2 < critDist (puAmalgam h.le))
    {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hγ : IsMVtx _ γ)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβγ : (puAmalgam h.le).treeGraph.Adj β γ)
    {x : 𝔘} (hx : x ∈ ZM (puAmalgam h.le) γ)
    (hc : ∀ w ∈ Vv (puAmalgam h.le) α, ∀ w' ∈ Vv (puAmalgam h.le) α, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w)
    (hnot : ¬ (commHomOf (Vv (puAmalgam h.le) α) x hc).range ≤ Zloc h.le L α)
    (hinv : ∀ g : 𝔘, IsOddL1 (puAmalgam h.le) α β g → ∀ y ∈ (commHomOf (Vv _ α) x hc).range,
      g * y * g⁻¹ ∈ (commHomOf (Vv (puAmalgam h.le) α) x hc).range ⊔ Zloc h.le L α) :
    (commHomOf (Vv (puAmalgam h.le) α) x hc).range = Usup (puAmalgam h.le) γ β ∧
      Usup (puAmalgam h.le) γ β ⊓ Zloc h.le L α = ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  set R := (commHomOf (Vv 𝔛 α) x hc).range with hRdef
  have hle := usup_le_range_sup_zloc h hφ h464 hsq h466 hb hα hγ hαβ hβγ hx hc hnot hinv
  have hRH : R ≤ Usup 𝔛 γ β := by
    rintro _ ⟨w, rfl⟩
    have hw : (w : 𝔘) ∈ Qv 𝔛 β := qv_le_qv _ h.hyp20 hα hαβ (vv_le_qv h hb hα w.2)
    rw [Usup, zv_of_isMVtx _ hγ]
    exact Subgroup.commutator_mem_commutator hx hw
  have hHZ : Usup 𝔛 γ β ≤ ZH 𝔛 β := h464 γ β hγ hβγ.symm
  have hZlZ : Zloc h.le L α ≤ ZH 𝔛 β := zloc_le_zh h hfull hα hαβ
  have hcomm : ∀ a ∈ ZH 𝔛 β, ∀ b ∈ ZH 𝔛 β, a * b = b * a := fun a ha b hb' =>
    commute_zh h ha hb'
  have : Finite ↥(stab 𝔛 α) := finite_stab h hα
  have hZs : ZH 𝔛 β ≤ stab 𝔛 α := (zh_le_zm _ hαβ).trans
    ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α))
  have : Finite ↥(ZH 𝔛 β) := finite_of_le_stab h hα hZs
  have : Finite ↥R := finite_of_le_stab h hα (hRH.trans (hHZ.trans hZs))
  have : Finite ↥(Usup 𝔛 γ β) := finite_of_le_stab h hα (hHZ.trans hZs)
  have : Finite ↥(Usup 𝔛 α β) := finite_of_le_stab h hα ((h464 α β hα hαβ).trans hZs)
  have : Finite ↥(Zloc h.le L α) := finite_of_le_stab h hα (hZlZ.trans hZs)
  have : Finite ↥(R ⊓ Zloc h.le L α) := finite_of_le_stab h hα (inf_le_right.trans (hZlZ.trans hZs))
  have hZβ : Nat.card ↥(ZH 𝔛 β) = Fintype.card F ^ 2 * Nat.card ↥(Zloc h.le L α) := by
    have h1 := card_sup_mul_card_inf_of_commute (H := Usup 𝔛 α β) (K := Zloc h.le L α)
      (fun a ha b hb' => hcomm a (h464 α β hα hαβ ha) b (hZlZ hb'))
    rw [usup_inf_zloc h hfull hα hαβ, Subgroup.card_bot, mul_one,
      ← zh_eq_usup_sup_zloc h hφ h464 hsq hα hαβ, hsq α β hα hαβ] at h1
    exact h1
  have hRsup : R ⊔ Zloc h.le L α = ZH 𝔛 β := by
    refine le_antisymm (sup_le (hRH.trans hHZ) hZlZ) ?_
    rw [zh_eq_usup_sup_zloc h hφ h464 hsq hα hαβ]
    exact sup_le hle le_sup_right
  have hRcard : Fintype.card F ^ 2 ≤ Nat.card ↥R := by
    have h1 := card_sup_mul_card_inf_of_commute (H := R) (K := Zloc h.le L α)
      (fun a ha b hb' => hcomm a (hRH.trans hHZ ha) b (hZlZ hb'))
    rw [hRsup, hZβ] at h1
    have hpos : 0 < Nat.card ↥(Zloc h.le L α) := Nat.card_pos
    have h2 : Fintype.card F ^ 2 * Nat.card ↥(Zloc h.le L α) ≤
        Nat.card ↥R * Nat.card ↥(Zloc h.le L α) := by
      rw [← h1]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    exact Nat.le_of_mul_le_mul_right h2 hpos
  have hReq : R = Usup 𝔛 γ β :=
    Subgroup.eq_of_le_of_card_ge hRH (by rw [hsq γ β hγ hβγ.symm]; exact hRcard)
  refine ⟨hReq, ?_⟩
  have h1 := card_sup_mul_card_inf_of_commute (H := Usup 𝔛 γ β) (K := Zloc h.le L α)
    (fun a ha b hb' => hcomm a (hHZ ha) b (hZlZ hb'))
  rw [← hReq, hRsup, hZβ, hReq, hsq γ β hγ hβγ.symm] at h1
  have hpos : 0 < Fintype.card F ^ 2 * Nat.card ↥(Zloc h.le L α) :=
    Nat.mul_pos (pow_pos Fintype.card_pos 2) Nat.card_pos
  have h2 : Nat.card ↥(Usup 𝔛 γ β ⊓ Zloc h.le L α) = 1 := by
    have := Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_one _).symm)
    exact this
  exact Subgroup.eq_bot_of_card_eq _ h2

omit [Fintype F] in
theorem zv_le_zm_of_dist_le_one {α ρ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hd : (puAmalgam h.le).treeGraph.dist α ρ ≤ 1) : Zv (puAmalgam h.le) ρ ≤ ZM _ α := by
  rcases (by omega : (puAmalgam h.le).treeGraph.dist α ρ = 0 ∨
      (puAmalgam h.le).treeGraph.dist α ρ = 1) with h0 | h1
  · rw [← (dist_eq_zero_iff _).mp h0, zv_of_isMVtx _ hα]
  · have hadj : (puAmalgam h.le).treeGraph.Adj α ρ := SimpleGraph.dist_eq_one_iff_adj.mp h1
    have hρ : ¬ IsMVtx 𝔛 ρ := (isMVtx_iff_of_adj _ hadj).mp hα
    rw [zv_of_not_isMVtx _ hρ]
    exact zh_le_zm _ hadj

include hφ in
theorem exists_commutator_not_mem_zloc (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (h466b : ¬ ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≤ stabCenter _ α) :
    ∃ β γ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj α β ∧
      (puAmalgam h.le).treeGraph.Adj β γ ∧ IsMVtx _ γ ∧
      ∃ x ∈ ZM (puAmalgam h.le) γ, ∃ w ∈ Vv (puAmalgam h.le) α, ⁅x, w⁆ ∉ Zloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  by_contra! hno
  apply h466b
  refine le_trans ?_ (zloc_le_stabCenter' h hfull hα)
  have hZn := stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α
  refine commutator_iSup₂_le_of (fun ρ hρ => ?_) (fun ρ hρ => ?_)
  · have hρ' : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 := hρ
    rw [Subgroup.commutator_le]
    intro x hx w hw
    by_cases h1 : (puAmalgam h.le).treeGraph.dist α ρ ≤ 1
    · have hxZ := zv_le_zm_of_dist_le_one h hα h1 hx
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (commute_zm_vv h hb hα hxZ hw)]
      exact one_mem _
    · have h2 : (puAmalgam h.le).treeGraph.dist α ρ = 2 := by omega
      have hρM : IsMVtx 𝔛 ρ := ((even_dist_iff _ α ρ).mp (by rw [h2]; decide)).mp hα
      rw [zv_of_isMVtx _ hρM] at hx
      have ha1 : (puAmalgam h.le).treeGraph.Adj α (geo 𝔛 α ρ 1) := by
        have := adj_geo 𝔛 (u := α) (w := ρ) (i := 0) (by omega)
        rwa [geo_zero] at this
      have ha2 : (puAmalgam h.le).treeGraph.Adj (geo 𝔛 α ρ 1) ρ := by
        have := adj_geo 𝔛 (u := α) (w := ρ) (i := 1) (by omega)
        rwa [show geo 𝔛 α ρ (1 + 1) = ρ from geo_of_le _ (by omega)] at this
      exact hno _ _ ha1 ha2 hρM x hx w hw
  · have hρ' : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 := hρ
    have : Zv 𝔛 ρ ≤ Vv 𝔛 α := le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx 𝔛 |
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv 𝔛 ρ) ρ hρ' le_rfl
    exact this.trans ((vv_le_qv h hb hα).trans ((qv_le_stab _ α).trans hZn))

include hφ h464 hsq h466 h463 in
theorem mem_centerOf_of_commutator_mem_zloc (hb4 : critDist (puAmalgam h.le) = 4)
    (h43 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h465 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
    (h466b : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ¬ ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ stabCenter _ x)
    (h467 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      Bloc h.le L x = centerOf (Vv (puAmalgam h.le) x))
    (h468 : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
      ∀ g : 𝔘, IsOddL1 (puAmalgam h.le) α β g → ∀ x ∈ Vv (puAmalgam h.le) β,
        ∀ v ∈ Vv (puAmalgam h.le) α, ⁅⁅x, g⁆, v⁆ ∈ stabCenter _ α)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {v : 𝔘} (hv : v ∈ Vv (puAmalgam h.le) α)
    (hvz : ∀ w ∈ Vv (puAmalgam h.le) α, ⁅v, w⁆ ∈ Zloc h.le L α) :
    v ∈ centerOf (Vv (puAmalgam h.le) α) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hC := centHyp_of_gen23 h hfull
  have hb : 2 < critDist 𝔛 := by omega
  have hb0 : 0 < critDist 𝔛 := by omega
  obtain ⟨β, γ, hαβ, hβγ, hγ, x, hx, w₀, hw₀, hxw₀⟩ :=
    exists_commutator_not_mem_zloc h hφ hb hα (h466b α hα)
  have hαγ : α ≠ γ := by
    rintro rfl
    apply hxw₀
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (commute_zm_vv h hb hα hx hw₀)]
    exact one_mem _
  have hd : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
  have hxV : x ∈ Vv 𝔛 α := zm_le_vv_of_dist_le_two hγ hd.le hx
  have hxVβ : x ∈ Vv 𝔛 β := zm_le_vv_of_adj hβγ hγ hx
  have hβH : ¬ IsMVtx 𝔛 β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hc : ∀ w ∈ Vv 𝔛 α, ∀ w' ∈ Vv 𝔛 α, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w := fun w hw w' hw' =>
    commute_commutator_vv h h463 hb hα hxV hw' hw
  set R := (commHomOf (Vv 𝔛 α) x hc).range with hRdef
  have hinv : ∀ g : 𝔘, IsOddL1 𝔛 α β g → ∀ y ∈ R, g * y * g⁻¹ ∈ R ⊔ Zloc h.le L α := by
    intro g hg y hy
    obtain ⟨w, hw, rfl⟩ := mem_range_commHomOf.mp hy
    have hgV : g * w * g⁻¹ ∈ Vv 𝔛 α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α hg.1) w).mp hw
    have hgVβ := normalizer_qv_le_normalizer_vv h hβH hg.2.1
    have hcβ : ⁅x, g⁆ ∈ Vv 𝔛 β := by
      have h1 : g * x⁻¹ * g⁻¹ ∈ Vv 𝔛 β :=
        (Subgroup.mem_normalizer_iff.mp hgVβ _).mp (Subgroup.inv_mem _ hxVβ)
      have e : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hxVβ h1
    have hcV : ⁅x, g⁆ ∈ Vv 𝔛 α := vv_le_vv_of_adj h hα hαβ hcβ
    have hcomm : ⁅x, g⁆⁻¹ * ⁅x, g * w * g⁻¹⁆ = ⁅x, g * w * g⁻¹⁆ * ⁅x, g⁆⁻¹ :=
      commute_commutator_vv h h463 hb hα hxV hgV (Subgroup.inv_mem _ hcV)
    rw [conj_commutatorElement_eq hcomm]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_range_commHomOf.mpr ⟨_, hgV, rfl⟩))
      (Subgroup.mem_sup_right ?_)
    have hcc : ⁅x, g⁆ * ⁅⁅x, g⁆, g * w * g⁻¹⁆ = ⁅⁅x, g⁆, g * w * g⁻¹⁆ * ⁅x, g⁆ :=
      commute_commutator_vv h h463 hb hα hcV hgV hcV
    rw [commutatorElement_inv_left_of_comm hcc]
    exact Subgroup.inv_mem _ (mem_zloc_of_mem_stabCenter h hφ hα
      (h463 α hα (Subgroup.commutator_mem_commutator hcV hgV))
      (h468 α β hα hαβ g hg x hxVβ _ hgV))
  have hnot : ¬ R ≤ Zloc h.le L α := fun hle =>
    hxw₀ (hle (mem_range_commHomOf.mpr ⟨w₀, hw₀, rfl⟩))
  obtain ⟨-, hHZ⟩ := range_eq_usup h hφ h464 hsq h466 hb hα hγ hαβ hβγ hx hc hnot hinv
  have hxw : x * w₀ ≠ w₀ * x := fun he => hxw₀ (by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr he]; exact one_mem _)
  have hw₀Q : w₀ ∉ Qv 𝔛 γ := fun hq =>
    hxw (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hγ hx) w₀ hq).symm
  have hVQ := not_vv_le_qv_of_not_commute h20 hb4 h43 hγ hd hx hw₀ hxw
  obtain ⟨α', hc', hgeo⟩ := exists_isCritical_of_not_vv_le_qv h20 hC hb4 hγ hd hVQ
  have hgeo1 : geo 𝔛 α α' 1 = β := eq_geo_one_of_adj hb4 hc' hαβ (by rw [hgeo]; exact hβγ)
  have hα' : IsMVtx 𝔛 α' := hc'.isMVtx_right _ h20
  let B₀ : Subgroup 𝔘 :=
    { carrier := {b | b ∈ Vv 𝔛 α ∧ ∀ w ∈ Vv 𝔛 α, ⁅b, w⁆ ∈ Zloc h.le L α}
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁, hb₁z⟩ ⟨hb₂, hb₂z⟩
        refine ⟨Subgroup.mul_mem _ hb₁ hb₂, fun w hw => ?_⟩
        rw [commutatorElement_mul_left_of_comm (commute_commutator_vv h h463 hb hα hb₂ hw hb₁)]
        exact Subgroup.mul_mem _ (hb₂z w hw) (hb₁z w hw)
      one_mem' := ⟨Subgroup.one_mem _, fun w _ => by simp⟩
      inv_mem' := by
        rintro b ⟨hb', hbz⟩
        refine ⟨Subgroup.inv_mem _ hb', fun w hw => ?_⟩
        rw [commutatorElement_inv_left_of_comm (commute_commutator_vv h h463 hb hα hb' hw hb')]
        exact Subgroup.inv_mem _ (hbz w hw) }
  have hBconj : ∀ g ∈ stab 𝔛 α, ∀ b ∈ B₀, g * b * g⁻¹ ∈ B₀ := by
    rintro g hg b ⟨hb', hbz⟩
    have hVn := stab_le_normalizer_vv h α hg
    refine ⟨(Subgroup.mem_normalizer_iff.mp hVn b).mp hb', fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ Vv 𝔛 α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α (Subgroup.inv_mem _ hg)) w).mp hw
    have e : ⁅g * b * g⁻¹, w⁆ = g * ⁅b, g⁻¹ * w * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, Subgroup.mem_centralizer_iff.mp
      (zloc_le_centralizer_stab h hfull hα (hbz _ hw')) g hg, mul_inv_cancel_right]
    exact hbz _ hw'
  have hB₀γ : B₀ ≤ Qv 𝔛 γ := by
    rintro b ⟨hb', hbz⟩
    have hbβ : b ∈ Qv 𝔛 β := qv_le_qv _ h20 hα hαβ (vv_le_qv h hb hα hb')
    rw [← hC γ β hγ hβγ.symm]
    refine ⟨hbβ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 : ⁅b, y⁆ ∈ Zloc h.le L α := hbz y (zm_le_vv_of_dist_le_two hγ hd.le hy)
    have h2 : ⁅b, y⁆ ∈ Usup 𝔛 γ β := by
      rw [Usup, zv_of_isMVtx _ hγ, ← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy hbβ)
    have h3 : ⁅b, y⁆ = 1 := by
      have : ⁅b, y⁆ ∈ Usup 𝔛 γ β ⊓ Zloc h.le L α := ⟨h2, h1⟩
      rwa [hHZ, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hB₀K : ⁅B₀, ZM 𝔛 α'⁆ ≤ ZM 𝔛 α := by
    rw [Subgroup.commutator_le]
    intro b hb' z hz
    have hzs : z ∈ stab 𝔛 α := zm_le_stab_of_isCritical _ h20 hb0 hc' hz
    have hzVγ : z ∈ Vv 𝔛 γ := zm_le_vv_of_dist_le_two hα'
      (by rw [← hgeo, dist_geo_crit_right hb4 hc' (by omega)]) hz
    have hcZ : ⁅b, z⁆ ∈ ZM 𝔛 γ := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (h465 γ hγ (Subgroup.commutator_mem_commutator hzVγ (hB₀γ hb')))
    have hcB : ⁅b, z⁆ ∈ B₀ := by
      have e : ⁅b, z⁆ = b * (z * b⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hb' (hBconj z hzs _ (Subgroup.inv_mem _ hb'))
    have hcC : ∀ w ∈ Vv 𝔛 α, ⁅b, z⁆ * w = w * ⁅b, z⁆ := by
      intro w hw
      have hwβ : w ∈ Qv 𝔛 β := qv_le_qv _ h20 hα hαβ (vv_le_qv h hb hα hw)
      have h1 : ⁅⁅b, z⁆, w⁆ ∈ Usup 𝔛 γ β := by
        rw [Usup, zv_of_isMVtx _ hγ]
        exact Subgroup.commutator_mem_commutator hcZ hwβ
      have h3 : ⁅⁅b, z⁆, w⁆ = 1 := by
        have : ⁅⁅b, z⁆, w⁆ ∈ Usup 𝔛 γ β ⊓ Zloc h.le L α := ⟨h1, hcB.2 w hw⟩
        rwa [hHZ, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp h3
    have hcβ : ⁅b, z⁆ ∈ ZH 𝔛 β := by
      by_contra hn
      exact hw₀Q (mem_qv_of_commute h hφ h464 hsq h466 hγ hβγ.symm hcZ hn
        (qv_le_qv _ h20 hα hαβ (vv_le_qv h hb hα hw₀)) (hcC w₀ hw₀).symm)
    exact zh_le_zm _ hαβ hcβ
  have hKρ : ZM 𝔛 α' ≤ Qv 𝔛 β := by
    have := zm_right_le_qv_geo h20 hb4 hc' (i := 1) le_rfl (by omega)
    rwa [hgeo1] at this
  have hKQ : ¬ ZM 𝔛 α' ≤ Qv 𝔛 α := (ms22_iii _ h20 hb0 hC hc').2.2
  have hA : stab 𝔛 α ≤ Subgroup.normalizer (B₀ : Set 𝔘) :=
    le_normalizer_of_map_conj_le fun g hg => by
      rintro _ ⟨b, hb', rfl⟩
      exact hBconj g hg b hb'
  have hL := commutator_ltil_le_of_commutator_le h hfull hα hαβ hA (stab_le_normalizer_zm _ α)
    hB₀K hKρ hKQ
  have hvB : v ∈ B₀ := ⟨hv, hvz⟩
  rw [← h467 α hα, mem_bloc_iff h hb hα]
  exact ⟨hv, fun l hl => hL (Subgroup.commutator_mem_commutator hvB hl)⟩

end B0

end CFSG.Quasithin.MS93.S46
