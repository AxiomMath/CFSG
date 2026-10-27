module

public import CFSG.Quasithin.MS93.S46I4610
public import CFSG.Quasithin.MS93.S46I467Dec
public import CFSG.Quasithin.MS93.S46X3Lin
public import CFSG.Quasithin.Background.G13Core
public import CFSG.Quasithin.Background.G1Module
public import CFSG.Quasithin.MS93.S46I466a
public import CFSG.Quasithin.MS93.S46Last
public import CFSG.Quasithin.MS93.S4A431G
public import CFSG.Quasithin.MS93.S4A433
public import CFSG.Quasithin.MS93.S4ABridge
public import CFSG.Quasithin.MS93.S4AL1

public section

namespace CFSG.Quasithin.MS93.S46.X3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

private theorem relIndex_sup_eq' {𝔾 : Type} [Group 𝔾] {H N : Subgroup 𝔾}
    (h : H ≤ Subgroup.normalizer (N : Set 𝔾)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

section Comm

variable {𝔾 : Type} [Group 𝔾]

@[expose] def commLeft (K N : Subgroup 𝔾) (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (g : 𝔾) :
    Subgroup 𝔾 where
  carrier := {y | y ∈ K ∧ ⁅y, g⁆ ∈ N}
  one_mem' := ⟨K.one_mem, by rw [commutatorElement_one_left]; exact N.one_mem⟩
  mul_mem' := fun {y y'} hy hy' => ⟨K.mul_mem hy.1 hy'.1, by
    rw [commutatorElement_mul_left_conj]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hy.1) _).mp hy'.2) hy.2⟩
  inv_mem' := fun {y} hy => ⟨K.inv_mem hy.1, by
    have e : ⁅y⁻¹, g⁆ = y⁻¹ * ⁅y, g⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hy.1)) _).mp (N.inv_mem hy.2)⟩

@[expose] def commRight (K N : Subgroup 𝔾) (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (x : 𝔾) :
    Subgroup 𝔾 where
  carrier := {k | k ∈ K ∧ ⁅x, k⁆ ∈ N}
  one_mem' := ⟨K.one_mem, by rw [commutatorElement_one_right]; exact N.one_mem⟩
  mul_mem' := fun {k k'} hk hk' => ⟨K.mul_mem hk.1 hk'.1, by
    rw [commutatorElement_mul_right_conj]
    exact N.mul_mem hk.2 ((Subgroup.mem_normalizer_iff.mp (hKN hk.1) _).mp hk'.2)⟩
  inv_mem' := fun {k} hk => ⟨K.inv_mem hk.1, by
    have e : ⁅x, k⁻¹⁆ = k⁻¹ * ⁅x, k⁆⁻¹ * k⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk.1)) _).mp (N.inv_mem hk.2)⟩

theorem commutator_mem_of_mem_sup {K A B N : Subgroup 𝔾}
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (hAK : A ≤ K) (hBK : B ≤ K) {g : 𝔾}
    (hA : ∀ a ∈ A, ⁅a, g⁆ ∈ N) (hB : ∀ b ∈ B, ⁅b, g⁆ ∈ N) {x : 𝔾} (hx : x ∈ A ⊔ B) :
    ⁅x, g⁆ ∈ N :=
  ((sup_le (fun a ha => ⟨hAK ha, hA a ha⟩) (fun b hb => ⟨hBK hb, hB b hb⟩) :
    A ⊔ B ≤ commLeft K N hKN g) hx).2

theorem le_normalizer_of_le_centralizer {Q S : Subgroup 𝔾}
    (hS : S ≤ Subgroup.centralizer (Q : Set 𝔾)) : Q ≤ Subgroup.normalizer (S : Set 𝔾) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have hc : ∀ s ∈ S, ∀ q ∈ Q, q * s * q⁻¹ = s := fun s hs q hq => by
    rw [Subgroup.mem_centralizer_iff.mp (hS hs) q hq, mul_inv_cancel_right]
  constructor
  · intro hs
    rw [hc s hs q hq]
    exact hs
  · intro hs
    have h1 := hc _ hs q⁻¹ (Q.inv_mem hq)
    have h2 : q⁻¹ * (q * s * q⁻¹) * q⁻¹⁻¹ = s := by group
    rw [← h2, h1]
    exact hs

end Comm

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem critDist_gt_two (c : Hyp46 M T L φ) : 2 < critDist (puAmalgam c.pu.le) := by
  have := c.b4
  omega

structure X3Data (c : Hyp46 M T L φ) (α β γ : Vtx (puAmalgam c.pu.le))
    (ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)) : Prop where
  mα : IsMVtx (puAmalgam c.pu.le) α
  adjαβ : (puAmalgam c.pu.le).treeGraph.Adj α β
  adjβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ
  zγ : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α
  lh : LastHyp (stab (puAmalgam c.pu.le) α) (Qv _ α) (Ltil c.pu.le L α) (Uloc c.pu.le L α)
    (Zloc c.pu.le L α) (ZM _ α) (Vv _ α) ψ
  qvβ : natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0
  tγ : Vv (puAmalgam c.pu.le) γ ⊔ Qv _ α = Qv _ β
  uγ : Usup (puAmalgam c.pu.le) γ β = Usup _ α β
  vqγ : ⁅Vv (puAmalgam c.pu.le) γ, Qv _ γ⁆ ≤ ZM _ γ
  idx : (ZM (puAmalgam c.pu.le) α).relIndex (ZM _ γ ⊔ ZM _ α) ≤ Fintype.card F
  uZ : Usup (puAmalgam c.pu.le) α β ≤ ZH _ β
  odd : ∀ g ∈ stab (puAmalgam c.pu.le) α,
    g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) →
    (∀ z ∈ ZM (puAmalgam c.pu.le) α, ⁅z, g⁆ ∈ ZH _ β) → Odd (orderOf g) →
      ∀ x ∈ Vv (puAmalgam c.pu.le) β, ⁅x, g⁆ ∈ ZH _ β
  star : vStar c.pu.le L α ⊓ Bloc c.pu.le L α ≤ ZM (puAmalgam c.pu.le) α

theorem X3Data.ofCfg (h463 : I463) (h464 : I464) (h465 : I465) (h466b : I466b) (h467 : I467)
    (h469 : I469Cfg M T L φ) (c : Hyp46 M T L φ) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ)
    (hZγ : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α)
    {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1)
    (hψT : natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0) :
    X3Data c α β γ ψ := by
  obtain ⟨hQL, -, hodd, h9⟩ := h469 c α β hα hαβ
  obtain ⟨-, hUU, hZαγ⟩ := h9 γ hβγ hZγ
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβγ
    tauto
  obtain ⟨-, -, -, h9'⟩ := h469 c γ β hγ hβγ.symm
  obtain ⟨hTγ, -, -⟩ := h9' α hαβ.symm hZαγ
  have hb4 := c.b4
  have hZγK : ZM (puAmalgam c.pu.le) γ ≤ stab _ α :=
    (zm_le_qv_of_dist_le_three hb4 hγ (by
      rw [tdist_comm]
      have hne : α ≠ γ := by
        rintro rfl
        exact hZγ (zm_le_bloc c.pu (by omega) hα)
      rw [dist_eq_two_of_adj_adj _ hαβ hβγ hne]
      omega)).trans (qv_le_stab _ α)
  have hidx : (ZM (puAmalgam c.pu.le) α).relIndex (ZM _ γ ⊔ ZM _ α) ≤ Fintype.card F := by
    rw [relIndex_sup_eq' (hZγK.trans (stab_le_normalizer_zm _ α))]
    have hq := (h465 G M T L F φ c γ β hγ hβγ.symm).2.1
    rw [← hq]
    exact Subgroup.relIndex_le_of_le_left (zh_le_zm _ hαβ)
      (by rw [hq]; exact Fintype.card_ne_zero)
  exact
    { mα := hα
      adjαβ := hαβ
      adjβγ := hβγ
      zγ := hZγ
      lh := lastHyp_of h463 h465 h466b h467 c hα hψs hψU hQL
      qvβ := hψT
      tγ := hTγ
      uγ := hUU
      vqγ := (h465 G M T L F φ c γ β hγ hβγ.symm).2.2
      idx := hidx
      uZ := h464 G M T L F φ c α β hα hαβ
      odd := hodd
      star := vStar_inf_bloc_le_cfg h463 h465 h466b h467 h469 c hα }

namespace X3Data

variable {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)} (d : X3Data c α β γ ψ)
include d

theorem mγ : IsMVtx (puAmalgam c.pu.le) γ := by
  have h1 := isMVtx_iff_of_adj _ d.adjαβ
  have h2 := isMVtx_iff_of_adj _ d.adjβγ
  have := d.mα
  tauto

theorem ne_αγ : α ≠ γ := by
  rintro rfl
  exact d.zγ (zm_le_bloc c.pu (critDist_gt_two c) d.mα)

theorem dist_αγ : (puAmalgam c.pu.le).treeGraph.dist α γ = 2 :=
  dist_eq_two_of_adj_adj _ d.adjαβ d.adjβγ d.ne_αγ

theorem qαβ : Qv (puAmalgam c.pu.le) α ≤ Qv _ β := qv_le_qv _ c.pu.hyp20 d.mα d.adjαβ

theorem qγβ : Qv (puAmalgam c.pu.le) γ ≤ Qv _ β := qv_le_qv _ c.pu.hyp20 d.mγ d.adjβγ.symm

theorem qβK : Qv (puAmalgam c.pu.le) β ≤ stab _ α := qv_le_stab_of_adj _ d.adjαβ.symm

theorem qβKγ : Qv (puAmalgam c.pu.le) β ≤ stab _ γ := qv_le_stab_of_adj _ d.adjβγ

theorem zγα : ZM (puAmalgam c.pu.le) γ ≤ Qv _ α :=
  zm_le_qv_of_dist_le_three c.b4 d.mγ (by rw [tdist_comm, d.dist_αγ]; omega)

theorem zγK : ZM (puAmalgam c.pu.le) γ ≤ stab _ α := d.zγα.trans (qv_le_stab _ α)

theorem vγβ : Vv (puAmalgam c.pu.le) γ ≤ Qv _ β :=
  (vv_le_qv c.pu (critDist_gt_two c) d.mγ).trans d.qγβ

theorem zγVβ : ZM (puAmalgam c.pu.le) γ ≤ Vv _ β := zm_le_vv_of_adj d.adjβγ d.mγ

theorem zγVα : ZM (puAmalgam c.pu.le) γ ≤ Vv _ α :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam c.pu.le) |
    (puAmalgam c.pu.le).treeGraph.dist α ρ ≤ 2}) => Zv _ ρ) γ (by simp [d.dist_αγ])
    (zv_of_isMVtx _ d.mγ).ge

theorem zγstar : ZM (puAmalgam c.pu.le) γ ≤ vStar c.pu.le L α :=
  le_iSup₂_of_le (f := fun β (_ : β ∈ (puAmalgam c.pu.le).treeGraph.neighborSet α) =>
    vStarB c.pu.le L α β) β d.adjαβ
    (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam c.pu.le) |
      (puAmalgam c.pu.le).treeGraph.Adj β ρ ∧ ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α}) =>
      ZM (puAmalgam c.pu.le) ρ) γ ⟨d.adjβγ, d.zγ⟩ le_rfl)

theorem zαstar : ZM (puAmalgam c.pu.le) α ≤ vStar c.pu.le L α := by
  refine iSup₂_le fun ρ hρ => ?_
  have hαρ : (puAmalgam c.pu.le).treeGraph.Adj α ρ := hρ
  obtain ⟨g, hg, rfl⟩ := I467.exists_mem_stab_smul_eq d.mα d.adjαβ hαρ
  have hgα : g • α = α := hg
  have hadj : (puAmalgam c.pu.le).treeGraph.Adj (g • β) (g • γ) :=
    (adj_smul _ g β γ).mpr d.adjβγ
  have hnB : ¬ ZM (puAmalgam c.pu.le) (g • γ) ≤ Bloc c.pu.le L α := by
    intro hle
    apply d.zγ
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rw [zm_smul, map_conj_inv_map_conj, ← hgα, bloc_smul c.pu, map_conj_inv_map_conj] at h1
    exact h1
  calc ZH (puAmalgam c.pu.le) (g • β) ≤ ZM _ (g • γ) := zh_le_zm _ hadj.symm
    _ ≤ vStarB c.pu.le L α (g • β) :=
        le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam c.pu.le) |
          (puAmalgam c.pu.le).treeGraph.Adj (g • β) ρ ∧
            ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α}) => ZM (puAmalgam c.pu.le) ρ)
          (g • γ) ⟨hadj, hnB⟩ le_rfl
    _ ≤ vStar c.pu.le L α :=
        le_iSup₂_of_le (f := fun β (_ : β ∈ (puAmalgam c.pu.le).treeGraph.neighborSet α) =>
          vStarB c.pu.le L α β) (g • β) hαρ le_rfl

theorem commutator_qv_le {X : Subgroup (puAmalgam c.pu.le).Universal} (hXV : X ≤ Vv _ α)
    (hXQ : X ≤ Qv (puAmalgam c.pu.le) γ) :
    ⁅X, Qv (puAmalgam c.pu.le) β⁆ ≤ ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α := by
  rw [Subgroup.commutator_comm, ← d.tγ]
  have hYn : Qv (puAmalgam c.pu.le) β ≤ Subgroup.normalizer
      ((ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α : Subgroup _) : Set (puAmalgam c.pu.le).Universal) :=
    CFSG.LieType.Steinberg.le_normalizer_sup (d.qβKγ.trans (stab_le_normalizer_zm _ γ))
      (d.qβK.trans (stab_le_normalizer_zm _ α))
  refine commutator_sup_le_of_le_normalizer hYn d.vγβ d.qαβ ?_ ?_
  · exact ((Subgroup.commutator_mono le_rfl hXQ).trans d.vqγ).trans le_sup_left
  · rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono hXV le_rfl).trans d.lh.vqc).trans le_sup_right

theorem commutator_sup_qv_le :
    ⁅ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α, Qv (puAmalgam c.pu.le) β⁆ ≤ ZM _ α := by
  have hn := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (d.qβK.trans (stab_le_normalizer_zm _ α))
  refine commutator_sup_le_of_le_normalizer (stab_le_normalizer_zm _ α) d.zγK d.lh.zK ?_ hn
  have e : ⁅ZM (puAmalgam c.pu.le) γ, Qv _ β⁆ = Usup _ γ β := by rw [Usup, zv_of_isMVtx _ d.mγ]
  rw [e, d.uγ, Usup, zv_of_isMVtx _ d.mα]
  exact hn

theorem mem_of_toSL3_eq {S : Subgroup (puAmalgam c.pu.le).Universal}
    (hQ : Qv (puAmalgam c.pu.le) α ≤ S) {s k : ↥(stab (puAmalgam c.pu.le) α)}
    (hs : (s : (puAmalgam c.pu.le).Universal) ∈ S) (he : toSL3 ψ s = toSL3 ψ k) :
    (k : (puAmalgam c.pu.le).Universal) ∈ S := by
  have h1 : toSL3 ψ (s⁻¹ * k) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have h2 := (d.lh.ker _).mp h1
  have e : (k : (puAmalgam c.pu.le).Universal) =
      (s : (puAmalgam c.pu.le).Universal) * ((s⁻¹ * k : ↥(stab (puAmalgam c.pu.le) α)) : _) := by
    simp
  rw [e]
  exact S.mul_mem hs (hQ h2)

theorem stab_le_of_natImage_eq_top {S : Subgroup (puAmalgam c.pu.le).Universal}
    (hQ : Qv (puAmalgam c.pu.le) α ≤ S) (hS : natImage ψ S = ⊤) :
    stab (puAmalgam c.pu.le) α ≤ S := by
  intro k hk
  obtain ⟨s, hs, he⟩ := mem_natImage.mp (hS ▸ Subgroup.mem_top (toSL3 ψ ⟨k, hk⟩))
  exact d.mem_of_toSL3_eq (k := ⟨k, hk⟩) hQ hs he

theorem mem_qv_of_toSL3 {k : ↥(stab (puAmalgam c.pu.le) α)}
    (hk : toSL3 ψ k ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) :
    (k : (puAmalgam c.pu.le).Universal) ∈ Qv _ β := by
  rw [← d.qvβ] at hk
  obtain ⟨t, ht, he⟩ := mem_natImage.mp hk
  exact d.mem_of_toSL3_eq d.qαβ ht he

theorem mem_normalizer_qv {k : ↥(stab (puAmalgam c.pu.le) α)}
    (hk : toSL3 ψ k ∈ Subgroup.normalizer
      ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F))) :
    (k : (puAmalgam c.pu.le).Universal) ∈
      Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) := by
  have key : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ Subgroup.normalizer
      ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) →
      ∀ t ∈ Qv (puAmalgam c.pu.le) β, (k : (puAmalgam c.pu.le).Universal) * t * (k : _)⁻¹ ∈
        Qv (puAmalgam c.pu.le) β := by
    intro k hk t ht
    have hts : t ∈ stab (puAmalgam c.pu.le) α := d.qβK ht
    have hR : toSL3 ψ ⟨t, hts⟩ ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
      rw [← d.qvβ]
      exact mem_natImage.mpr ⟨⟨t, hts⟩, ht, rfl⟩
    have := d.mem_qv_of_toSL3 (k := k * ⟨t, hts⟩ * k⁻¹) (by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hk _).mp hR)
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact key k hk t
  · intro ht
    have := key k⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hk) _ ht
    simpa [mul_assoc] using this

theorem exists_lift_rot {a : F} (ha : a ≠ 0) :
    ∃ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k = rootElt 1 2 a * rootElt 2 1 a⁻¹ ∧
      ∀ x ∈ ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α,
        ⁅x, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hB3 : (rootElt 1 2 a * rootElt 2 1 a⁻¹ : SL3 F) ^ 3 = 1 :=
    rootElt12_mul_rootElt21_pow_three ha
  obtain ⟨k₀, hk₀⟩ := toSL3_surjective d.lh.surj (rootElt 1 2 a * rootElt 2 1 a⁻¹)
  have h3 : toSL3 ψ (k₀ ^ 3) = 1 := by rw [map_pow, hk₀, hB3]
  obtain ⟨e, he⟩ := pow_two_pow_eq_one_of_toSL3_eq_one c.pu c.via d.mα d.lh.nat _ h3
  have hmod : 2 ^ e * 2 ^ e % 3 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  set k : ↥(stab (puAmalgam c.pu.le) α) := k₀ ^ (2 ^ e * 2 ^ e) with hk
  have hk3 : k ^ 3 = 1 := by
    rw [hk, ← pow_mul, show 2 ^ e * 2 ^ e * 3 = 3 * 2 ^ e * 2 ^ e by ring, pow_mul, pow_mul, he,
      one_pow]
  have hψk : toSL3 ψ k = rootElt 1 2 a * rootElt 2 1 a⁻¹ := by
    rw [hk, map_pow, hk₀, pow_eq_pow_mod _ hB3, hmod, pow_one]
  have hodd : Odd (orderOf (k : (puAmalgam c.pu.le).Universal)) := by
    have h1 : (k : (puAmalgam c.pu.le).Universal) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hk3, Subgroup.coe_one]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1) with h | h <;>
      rw [h] <;> decide
  have hN := d.mem_normalizer_qv (k := k) (by
    rw [hψk]
    exact Subgroup.mul_mem _ (rootElt12_mem_normalizer a) (rootElt21_mem_normalizer a⁻¹))
  have hZ : ∀ z ∈ ZM (puAmalgam c.pu.le) α,
      ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZH (puAmalgam c.pu.le) β := by
    intro z hz
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc c.pu hfull d.mα hz
    set kk : (puAmalgam c.pu.le).Universal := (k : (puAmalgam c.pu.le).Universal) with hkk
    have hζk : ζ * kk = kk * ζ := (d.lh.comm_z0_k hζ k.2).symm
    have e1 : ⁅u * ζ, kk⁆ = ⁅u, kk⁆ := by
      simp only [commutatorElement_def]
      calc u * ζ * kk * (u * ζ)⁻¹ * kk⁻¹ = u * (ζ * kk) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by group
        _ = u * (kk * ζ) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by rw [hζk]
        _ = u * kk * u⁻¹ * kk⁻¹ := by group
    rw [e1]
    have hmem : ⁅u, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ Uloc c.pu.le L α :=
      I467.commutator_mem_of_natural d.lh.nat ⟨u, hu⟩ k
    have hnat := natVec_commutator d.lh.nat k ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    have hc : natVec d.lh.nat ⟨_, hmem⟩ ∈ commN (natImage ψ (Qv (puAmalgam c.pu.le) β)) := by
      rw [d.qvβ]
      apply mem_commN_of_apply_zero
      rw [hnat, hψk, Pi.sub_apply, rootElt12_mul_rootElt21_mulVec_apply_zero, sub_self]
    have h1 := (mem_commutator_iff_natVec d.lh.nat d.qβK ⟨_, hmem⟩).mpr hc
    rw [← usup_eq_commutator_uloc c.pu hfull d.mα d.adjαβ] at h1
    exact d.uZ h1
  have hV := d.odd (k : (puAmalgam c.pu.le).Universal) k.2 hN hZ hodd
  refine ⟨k, hψk, fun x hx => ?_⟩
  refine commutator_mem_of_mem_sup (stab_le_normalizer_zm _ α) d.zγK d.lh.zK
    (fun z hz => zh_le_zm _ d.adjαβ (hV z (d.zγVβ hz))) (fun z hz => ?_) hx
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp (stab_le_normalizer_zm _ α)
    (Subgroup.commutator_mem_commutator hz k.2)

theorem commutator_mem_of_rootGroup12
    (h21 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    {k : ↥(stab (puAmalgam c.pu.le) α)}
    (hk : toSL3 ψ k ∈ (rootGroup 1 2 : Subgroup (SL3 F))) {z : (puAmalgam c.pu.le).Universal}
    (hz : z ∈ ZM (puAmalgam c.pu.le) γ) :
    ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  set S := commRight (stab (puAmalgam c.pu.le) α) (ZM _ α) (stab_le_normalizer_zm _ α) z with hS
  have hQS : Qv (puAmalgam c.pu.le) α ≤ S := fun q hq =>
    ⟨d.lh.qK hq, d.lh.vqc (Subgroup.commutator_mem_commutator (d.zγVα hz) hq)⟩
  obtain ⟨a, ha⟩ := hk
  by_cases ha0 : a = 0
  · have h1 : toSL3 ψ k = 1 := by rw [← ha, ha0, rootElt_zero]
    exact (hQS ((d.lh.ker k).mp h1)).2
  · obtain ⟨k₃, hk₃, hk₃z⟩ := d.exists_lift_rot ha0
    obtain ⟨k₂, hk₂⟩ := toSL3_surjective d.lh.surj (rootElt 2 1 a⁻¹)
    have hs : ((k₃ * k₂ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) ∈ S :=
      S.mul_mem ⟨k₃.2, hk₃z z (Subgroup.mem_sup_left hz)⟩
        ⟨k₂.2, h21 k₂ (hk₂ ▸ rootElt_mem_rootGroup 2 1 a⁻¹) z hz⟩
    have he : toSL3 ψ (k₃ * k₂) = toSL3 ψ k := by
      rw [map_mul, hk₃, hk₂, mul_assoc, rootElt_mul_self, mul_one, ha]
    exact (d.mem_of_toSL3_eq hQS hs he).2

theorem apply_zero_of_mem_usup {g : ↥(stab (puAmalgam c.pu.le) α)} {u : ↥(Uloc c.pu.le L α)}
    (hu : (u : (puAmalgam c.pu.le).Universal) ∈
      Usup (puAmalgam c.pu.le) α ((g : (puAmalgam c.pu.le).Universal) • β)) :
    ((((toSL3 ψ g)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec d.lh.nat u) 0 = 0 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hgα : (g : (puAmalgam c.pu.le).Universal) • α = α := g.2
  have e : Usup (puAmalgam c.pu.le) α ((g : (puAmalgam c.pu.le).Universal) • β) =
      (Usup (puAmalgam c.pu.le) α β).map
        (MulAut.conj (g : (puAmalgam c.pu.le).Universal)).toMonoidHom := by
    rw [← usup_smul, hgα]
  rw [e, mem_map_conj] at hu
  have hmem : ((g⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) * u *
      ((g⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ ∈
      Uloc c.pu.le L α := d.lh.conj_mem_u u.2 (g⁻¹).2
  have hnat := natVec_conj d.lh.nat g⁻¹ u ⟨_, hmem⟩ rfl
  have hu' : ((⟨_, hmem⟩ : ↥(Uloc c.pu.le L α)) : (puAmalgam c.pu.le).Universal) ∈
      ⁅Uloc c.pu.le L α, Qv (puAmalgam c.pu.le) β⁆ := by
    rw [← usup_eq_commutator_uloc c.pu hfull d.mα d.adjαβ]
    simpa using hu
  have hc := (mem_commutator_iff_natVec d.lh.nat d.qβK _).mp hu'
  rw [d.qvβ, hnat, map_inv] at hc
  exact apply_zero_of_mem_commN hc

theorem mem_qv_of_commute {x : (puAmalgam c.pu.le).Universal}
    (hx : x ∈ Vv (puAmalgam c.pu.le) α)
    (hc : ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅x, z⁆ = 1) : x ∈ Qv (puAmalgam c.pu.le) γ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hxs : x ∈ stab (puAmalgam c.pu.le) γ :=
    d.qβKγ (d.qαβ (d.lh.vq hx))
  refine stab_inf_centralizer_uloc_le_qv c.pu c.via d.mγ
    (Subgroup.mem_inf.mpr ⟨hxs, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩)
  have h1 := hc u (uloc_le_zm c.pu hfull d.mγ hu)
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end X3Data

end CFSG.Quasithin.MS93.S46.X3
