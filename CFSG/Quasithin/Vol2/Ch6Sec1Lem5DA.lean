module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Cut
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5C
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QLine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem exists_hall_ch615 (c : Cx615B G T M L V H n) :
    ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (borelL T L) := by
  have hTLB : T ⊓ L ≤ borelL T L := le_inf inf_le_right fun x hx => Subgroup.le_normalizer hx
  have hsylB : IsSylowTwoOf (T ⊓ L) (borelL T L) :=
    A4.isSylowTwoOf_mono c.toCx615.isSylowTwoOf_inf hTLB inf_le_left
  exact Lin2.exists_hall_of_normal_sylow hsylB inf_le_right

theorem commutator_thompsonJ_ne_ch615 (c : Cx615B G T M L V H n) :
    ⁅V, thompsonJ T⁆ ≠ ⊥ := by
  have h := c.hyp
  intro hVJ
  apply h.module.2.2
  have hJV : thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hVJ
    exact hVJ
  have hJO : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← h.centralizer_eq]
    exact le_inf (GammaExtra.thompsonJ_le fun A hA => hA.1) hJV
  have hLO : L ≤ pCoreOf 2 (L ⊔ T) := by
    have h1 : ⁅L, thompsonJ T⁆ ≤ pCoreOf 2 (L ⊔ T) :=
      (Subgroup.commutator_mono le_rfl hJO).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          (le_sup_left.trans (le_normalizer_pCoreOf 2 (L ⊔ T))))
    rwa [c.JL] at h1
  have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [← h.centralizer_eq] at hLO
    exact hLO.trans inf_le_right
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC

theorem inf_le_baum_ch615 (hR1 : L2RankOneSylowFact) (c : Cx615B G T M L V H n) :
    T ⊓ L ≤ baum T := by
  have h := c.hyp
  have hsyl := stmt5_1_7_one_nat_of_rankOne hR1 G T M L V n h.toHyp5_0_1 h.module
    c.commutator_thompsonJ_ne_ch615 c.nat
  have hle : baum T ⊓ L ≤ T ⊓ L := inf_le_inf_right L inf_le_left
  have heq : baum T ⊓ L = T ⊓ L :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (hsyl.card_eq.trans c.toCx615.isSylowTwoOf_inf.card_eq.symm).symm)
  rw [← heq]
  exact inf_le_left


theorem commutator_Z_eq_ch615 (c : Cx615B G T M L V H n) :
    ⁅quasithinOmegaOneCenter T, L⁆ = ⁅V, L⁆ := by
  classical
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans c.toCx615.V_facts.2.1
  set Z := quasithinOmegaOneCenter T with hZdef
  set W := ⁅Z, L⁆ with hWdef
  have hZV : Z ≤ V := c.ZV
  have hWV : W ≤ V := (Subgroup.commutator_mono hZV le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hLV)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right Z L
  refine le_antisymm (Subgroup.commutator_mono hZV le_rfl) ?_
  obtain ⟨F, _, _, _, -, ψ, Y, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hYk := hc.ker
  let act : ↥L →* ↥(autOn L V) := (A4.actionOn V L hLV).codRestrict (autOn L V)
    (fun l => (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩)
  have hact : ∀ (l : ↥L) (w : ↥V), ((((act l : ↥(autOn L V)) : MulAut ↥V) w : ↥V) : G) =
      l * w * (l : G)⁻¹ := fun l w => rfl
  have hsurj : ∀ x : ↥(autOn L V), ∃ l : ↥L, act l = x := fun x => by
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp x.2
    exact ⟨l, Subtype.ext hl⟩
  have hcomm : ∀ (l : ↥L) (w : ↥V) (hw : (l : G) * w * (l : G)⁻¹ * (w : G)⁻¹ ∈ V),
      Multiplicative.toAdd (Y ⟨(l : G) * w * (l : G)⁻¹ * (w : G)⁻¹, hw⟩) =
        (ψ (act l) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y w)) -
          Multiplicative.toAdd (Y w) := by
    intro l w hw
    have e : (⟨(l : G) * w * (l : G)⁻¹ * (w : G)⁻¹, hw⟩ : ↥V) =
        ((act l : ↥(autOn L V)) : MulAut ↥V) w * w⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hact])
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hc.intertwine, sub_eq_add_neg]
  obtain ⟨z, hz, hzL⟩ : ∃ z ∈ Z ⊓ ⁅V, L⁆, z ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hall
    exact c.ZL fun x hx => by
      by_contra hxL
      exact hall ⟨x, hx, hxL⟩
  have hzV : z ∈ V := hZV hz.1
  set y₀ := Multiplicative.toAdd (Y ⟨z, hzV⟩) with hy₀
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := (mem_quasithinOmegaOneCenter_iff.mp hz.1).2.1
  have hy₀1 : y₀ 1 = 0 := by
    refine (hc.snd_eq_zero_iff inf_le_right ⟨z, hzV⟩).mpr fun s hs => ?_
    have hsz : s * z * s⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp hzT s hs.1, mul_inv_cancel_right]
    show s * z * s⁻¹ * z⁻¹ ∈ _
    rw [hsz, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hy₀0 : y₀ 0 ≠ 0 := by
    intro h0
    apply hzL
    have h1 : Y ⟨z, hzV⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact h0
      · exact hy₀1
    exact (hYk _).mp h1
  set YW := (W.subgroupOf V).map Y
  have hmemYW : ∀ (w : G) (hw : w ∈ W), Y ⟨w, hWV hw⟩ ∈ YW := fun w hw =>
    ⟨⟨w, hWV hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  have hpre : ∀ γ : SL(2, F), ∃ l : ↥L, ψ (act l) = γ := fun γ => by
    obtain ⟨l, hl⟩ := hsurj (ψ.symm γ)
    exact ⟨l, by rw [hl, MulEquiv.apply_symm_apply]⟩
  have hcol1 : ∀ b : F, Multiplicative.ofAdd ![0, b] ∈ YW := by
    intro b
    set a := y₀ 0 with ha
    let γ : SL(2, F) := ⟨!![1, 0; b / a, 1], by simp [Matrix.det_fin_two]⟩
    obtain ⟨l, hl⟩ := hpre γ
    have hw : (l : G) * z * (l : G)⁻¹ * z⁻¹ ∈ W := by
      have := Subgroup.commutator_mem_commutator l.2 hz.1
      rw [Subgroup.commutator_comm] at this
      rwa [commutatorElement_def] at this
    have h1 := hcomm l ⟨z, hzV⟩ (hWV hw)
    rw [hl] at h1
    have h2 : Y ⟨(l : G) * z * (l : G)⁻¹ * z⁻¹, hWV hw⟩ = Multiplicative.ofAdd ![0, b] := by
      apply Multiplicative.toAdd.injective
      rw [h1, toAdd_ofAdd]
      funext i
      fin_cases i
      · simp [γ, dotProduct, Fin.sum_univ_two, ← hy₀, hy₀1]
      · simp [γ, dotProduct, Fin.sum_univ_two, ← hy₀, hy₀1, ← ha,
          div_mul_cancel₀ b hy₀0]
    rw [← h2]
    exact hmemYW _ hw
  have hcol0 : ∀ b : F, Multiplicative.ofAdd ![b, 0] ∈ YW := by
    intro b
    obtain ⟨⟨w₁, hw₁V⟩, hw₁W, hw₁⟩ := hcol1 1
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw₁W
    obtain ⟨l, hl⟩ := hpre (unipSL b)
    have hw : (l : G) * w₁ * (l : G)⁻¹ * w₁⁻¹ ∈ W := by
      have h1 : (l : G) * w₁ * (l : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hLW l.2) w₁).mp hw₁W
      exact W.mul_mem h1 (W.inv_mem hw₁W)
    have h1 := hcomm l ⟨w₁, hw₁V⟩ (hWV hw)
    rw [hl, hw₁, coe_unipSL] at h1
    have h2 : Y ⟨(l : G) * w₁ * (l : G)⁻¹ * w₁⁻¹, hWV hw⟩ = Multiplicative.ofAdd ![b, 0] := by
      apply Multiplicative.toAdd.injective
      rw [h1, toAdd_ofAdd]
      funext i
      fin_cases i <;> simp
    rw [← h2]
    exact hmemYW _ hw
  have hYWtop : ∀ v : ↥V, Y v ∈ YW := by
    intro v
    have e : Y v = Multiplicative.ofAdd ![(Multiplicative.toAdd (Y v)) 0, 0] *
        Multiplicative.ofAdd ![0, (Multiplicative.toAdd (Y v)) 1] := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
      funext i
      fin_cases i <;> simp
    rw [e]
    exact YW.mul_mem (hcol0 _) (hcol1 _)
  have hVW : ∀ v ∈ V, ∃ w ∈ W, w⁻¹ * v ∈ Subgroup.centralizer (L : Set G) := by
    intro v hv
    obtain ⟨⟨w, hwV⟩, hwW, hwv⟩ := hYWtop ⟨v, hv⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hwW
    refine ⟨w, hwW, ?_⟩
    have h1 : Y (⟨w, hwV⟩⁻¹ * ⟨v, hv⟩) = 1 := by rw [map_mul, map_inv, hwv, inv_mul_cancel]
    exact (hYk _).mp h1
  rw [Subgroup.commutator_le]
  intro v hv l hl
  obtain ⟨w, hwW, hwv⟩ := hVW v hv
  have hul : (w⁻¹ * v) * l = l * (w⁻¹ * v) := (Subgroup.mem_centralizer_iff.mp hwv l hl).symm
  have e : ⁅v, l⁆ = ⁅w, l⁆ := by
    have hv' : v = w * (w⁻¹ * v) := by group
    rw [commutatorElement_def, commutatorElement_def]
    conv_lhs => rw [hv']
    calc w * (w⁻¹ * v) * l * (w * (w⁻¹ * v))⁻¹ * l⁻¹ =
        w * ((w⁻¹ * v) * l) * (w⁻¹ * v)⁻¹ * w⁻¹ * l⁻¹ := by group
      _ = w * (l * (w⁻¹ * v)) * (w⁻¹ * v)⁻¹ * w⁻¹ * l⁻¹ := by rw [hul]
      _ = w * l * w⁻¹ * l⁻¹ := by group
  rw [e]
  exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hLW)
    (Subgroup.commutator_mem_commutator hwW hl)


theorem isPGroup_borelL_inf_ch615 (c : Cx615B G T M L V H n) :
    IsPGroup 2 ↥(borelL T L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  rintro ⟨b, hbB, hbZ⟩
  obtain ⟨k, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
  have hb' : (b ^ 2 ^ k) ^ m = 1 := by rw [← pow_mul, ← hbm, pow_orderOf_eq_one]
  have hodd : Odd (orderOf (b ^ 2 ^ k)) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hb')
  have hb1 : b ^ 2 ^ k = 1 := by
    by_contra hne
    apply c.ZL
    intro z hz
    refine c.CZd _ ((borelL T L).pow_mem hbB _) hodd hne ⟨hz.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    rw [Set.mem_singleton_iff.mp hg]
    exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer _).pow_mem hbZ _) z hz.1).symm
  exact ⟨k, Subtype.ext (by simpa using hb1)⟩

end Cx615B

end CFSG.Quasithin.H13
