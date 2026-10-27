module

public import CFSG.Milestones.ASVolI.F4K.F415
public import CFSG.Milestones.ASVolI.F4K.Grp
public import CFSG.Milestones.ASVolI.F4N.BId
public import CFSG.Milestones.ASVolI.F4N.L23

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF4n_F422Facts : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → (κ = .G2d ∨ κ = .Tits) →
      Nat.card M₁ ≠ 10 ∧ Nat.card M₁ ≠ 3 ∧
        ∀ N : Subgroup E, N.Normal → N ≤ M₁ ⊓ M₂ → N = ⊥

theorem burnsideF4n_fix_lines {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y]
    {c : α.Completion Y}
    {m : ℕ} (F : c.Facts46 m) (hm : 2 < m) {z : c.G0}
    (hz : ∀ v : c.Γ, CosetGeom.vtype v = false → z • v = v) (w : c.Γ) : z • w = w := by
  cases hw : CosetGeom.vtype w
  · exact hz w hw
  · obtain ⟨v₁, v₂, h1, h2, hne⟩ := F.exists_two_nbrs w
    have hv₁ : CosetGeom.vtype v₁ = false := by
      have := CosetGeom.vtype_ne_of_adj h1
      rw [hw] at this
      simpa using this.symm
    have hv₂ : CosetGeom.vtype v₂ = false := by
      have := CosetGeom.vtype_ne_of_adj h2
      rw [hw] at this
      simpa using this.symm
    by_contra hzw
    let walk₁ : c.graph.Walk v₁ v₂ :=
      SimpleGraph.Walk.cons h1.symm (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)
    let q₁ : GPath c.graph 2 := GPath.ofWalk walk₁
    have h1' : c.graph.Adj v₁ (z • w) := by
      have := (CosetGeom.smul_adj z).mpr h1.symm
      rwa [hz v₁ hv₁] at this
    have h2' : c.graph.Adj (z • w) v₂ := by
      have := (CosetGeom.smul_adj z).mpr h2
      rwa [hz v₂ hv₂] at this
    let walk₂ : c.graph.Walk v₁ v₂ :=
      SimpleGraph.Walk.cons h1' (SimpleGraph.Walk.cons h2' SimpleGraph.Walk.nil)
    let q₂ : GPath c.graph 2 := GPath.ofWalk walk₂
    have hq₁ : q₁ ∈ GPath.nbPaths c.graph v₁ 2 := by
      refine ⟨rfl, fun i hi => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      exact hne
    obtain ⟨hd, huniq⟩ := F.uniq 2 hm v₁ q₁ hq₁
    have hgeo : q₂.IsGeodesic := by
      show c.graph.dist (q₂ 0) (q₂ 2) = 2
      exact hd
    have heq := huniq q₂ rfl rfl hgeo
    have := congrArg (fun r : GPath c.graph 2 => r 1) heq
    exact hzw this

theorem burnsideF4n_F422_of_facts
    (h45 : F_4_5) (h46 : F_4_6)
    (hfacts : burnsideF4n_F422Facts) : F_4_22 := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ Y _ β hβ hs
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := burnsideF4n_facts46_at h46 hyp β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  obtain ⟨hc10, hc3, hN⟩ := hfacts κ p f E Gp M₁ M₂ hyp hGp hκ
  have hm : 2 < κ.m := by rcases hκ with rfl | rfl <;> decide
  have h58 := (h46 κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).2.2.2.2
  have hzx : ∀ z ∈ Subgroup.center β.G0, z • β.xv = β.xv := by
    intro z hz
    by_contra hne
    set u := z • β.xv with hu
    have hfix : ∀ g ∈ stv β β.xv, g • u = u := by
      intro g hg
      rw [hu, ← mul_smul, Subgroup.mem_center_iff.mp hz g, mul_smul,
        MulAction.mem_stabilizer_iff.mp hg]
    have hdle : β.graph.dist β.xv u ≤ κ.m := F.diam_le hs β.xv u
    rcases Nat.lt_or_ge (β.graph.dist β.xv u) κ.m with hlt | hge
    ·
      obtain ⟨q, hq0, hqn, hqnb⟩ := GPath.exists_geodesic (connected_graph β) β.xv u
      have hn0 : β.graph.dist β.xv u ≠ 0 := by
        intro h0
        exact hne ((SimpleGraph.Reachable.dist_eq_zero_iff
          ((connected_graph β).preconnected β.xv u)).mp h0).symm
      have hadj : β.graph.Adj β.xv (q 1) := by
        have := q.adj 0 (by omega)
        rwa [hq0] at this
      obtain ⟨w, hw, hw1, -⟩ := F.hval β.xv (q 1) (q 1)
      obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq hadj hw
      obtain ⟨hd, huniq⟩ := F.uniq _ hlt β.xv q ⟨hq0, hqnb⟩
      have hgeo : (g • q).IsGeodesic := by
        show β.graph.dist ((g • q) 0) ((g • q) _) = _
        rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul (connected_graph β), hq0, hqn]
      have heq := huniq (g • q) (by rw [GPath.smul_apply, hq0, hg1])
        (by rw [GPath.smul_apply, hqn, hfix g (MulAction.mem_stabilizer_iff.mpr hg1)]) hgeo
      have h1 : (g • q) 1 = q 1 := by rw [heq]
      rw [GPath.smul_apply, hg2] at h1
      exact hw1 h1
    ·
      have hdm : β.graph.dist β.xv u = κ.m := le_antisymm hdle hge
      obtain ⟨q, hq0, hqm, hqnb⟩ := GPath.exists_geodesic' (connected_graph β) β.xv u hdm
      have hq : q ∈ GPath.nbPaths β.graph β.xv κ.m := ⟨hq0, hqnb⟩
      have hstab : stv β β.xv ⊓ stv β (q κ.m) = stv β β.xv := by
        rw [hqm]
        exact inf_eq_left.mpr fun g hg => MulAction.mem_stabilizer_iff.mpr (hfix g hg)
      rcases (h58 β.xv q hq).2.2.2 with huq | ⟨-, h2t, -⟩ | ⟨-, -, ⟨e⟩, -⟩ | ⟨-, -, ⟨e⟩, -⟩
      ·
        obtain ⟨t₁, t₂, ht₁, ht₂, hne12⟩ := F.lemma_F412 hs β.xv u hdm
        have e1 := huq t₁ ht₁.1 (by rw [ht₁.2.1, hqm]) ht₁.2.2
        have e2 := huq t₂ ht₂.1 (by rw [ht₂.2.1, hqm]) ht₂.2.2
        exact hne12 (e1.trans e2.symm)
      ·
        exact burnsideF4k_asm_not_ii burnsideF4k_grpTwoTrans h46 h45 ChF.nativeChartCompatibility
          hyp hκ.symm β hβ hs hq h2t
      ·
        rw [hstab] at e
        apply hc10
        have := Nat.card_congr e.toEquiv
        rw [card_stv_xv β hβ] at this
        rw [show Nat.card (DihedralGroup 5) = 10 by rw [Nat.card_eq_fintype_card,
          DihedralGroup.card]] at this
        exact this
      ·
        rw [hstab] at e
        apply hc3
        have := Nat.card_congr e.toEquiv
        rw [card_stv_xv β hβ] at this
        rw [show Nat.card (Multiplicative (ZMod 3)) = 3 by simp] at this
        exact this
  have hzall : ∀ z ∈ Subgroup.center β.G0, ∀ v : β.Γ, z • v = v := by
    intro z hz
    refine burnsideF4n_fix_lines F hm fun v hv => ?_
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert β v
    rw [hv] at hg
    rw [← hg]
    show z • (g • β.xv) = g • β.xv
    rw [← mul_smul, ← Subgroup.mem_center_iff.mp hz g, mul_smul, hzx z hz]
  let Kβ : Subgroup β.G0 := (MulAction.toPermHom β.G0 β.Γ).ker
  have hKmem : ∀ g : β.G0, g ∈ Kβ ↔ ∀ v : β.Γ, g • v = v := by
    intro g
    rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
    rfl
  have hKn : Kβ.Normal := MonoidHom.normal_ker _
  let ι₁ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 →* E := M₁.subtype
  let ι₂ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 →* E := M₂.subtype
  have hι : ∀ x : (RankTwoAmalgam.ofSubgroups M₁ M₂).G12,
      ι₁ ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 x) = ι₂ ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 x) :=
    fun _ => rfl
  let N : Subgroup E := (Kβ.comap (f1 (c := β))).map ι₁
  have hNle : N ≤ M₁ ⊓ M₂ := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := (burnsideF4n_f1_smul_lv_iff β hβ a).mp ((hKmem _).mp ha β.lv)
    obtain ⟨d, rfl⟩ := h1
    exact d.2
  have hconj1 : ∀ g ∈ M₁, ∀ e ∈ N, g * e * g⁻¹ ∈ N := by
    intro g hg e he
    obtain ⟨m, rfl⟩ : ∃ m : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1, ι₁ m = g :=
      ⟨(⟨g, hg⟩ : ↥M₁), rfl⟩
    obtain ⟨a, ha, rfl⟩ := he
    refine ⟨m * a * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    show f1 (c := β) (m * a * m⁻¹) ∈ Kβ
    rw [map_mul, map_mul, map_inv]
    exact hKn.conj_mem _ ha _
  have hconj2 : ∀ g ∈ M₂, ∀ e ∈ N, g * e * g⁻¹ ∈ N := by
    intro g hg e he
    obtain ⟨m, rfl⟩ : ∃ m : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, ι₂ m = g :=
      ⟨(⟨g, hg⟩ : ↥M₂), rfl⟩
    have he12 := hNle he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨d, rfl⟩ := (burnsideF4n_f1_smul_lv_iff β hβ a).mp ((hKmem _).mp ha β.lv)
    have hk : f2 (c := β) (m * (RankTwoAmalgam.ofSubgroups M₁ M₂).α2 d * m⁻¹) ∈ Kβ := by
      rw [map_mul, map_mul, map_inv, ← burnsideF4n_f1_alpha1]
      exact hKn.conj_mem _ ha _
    obtain ⟨d', hd'⟩ := (burnsideF4n_f2_smul_xv_iff β hβ _).mp ((hKmem _).mp hk β.xv)
    refine ⟨(RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d', ?_, ?_⟩
    · show f1 (c := β) _ ∈ Kβ
      rw [burnsideF4n_f1_alpha1, hd']
      exact hk
    · rw [hι d', hι d, hd', map_mul, map_mul, map_inv]
  have hNnorm : N.Normal := by
    have hnorm : ∀ (H : Subgroup E), (∀ g ∈ H, ∀ e ∈ N, g * e * g⁻¹ ∈ N) →
        H ≤ Subgroup.normalizer (N : Set E) := by
      intro H hH g hg
      rw [Subgroup.mem_normalizer_iff]
      intro e
      refine ⟨fun he => hH g hg e he, fun he => ?_⟩
      have := hH g⁻¹ (H.inv_mem hg) _ he
      rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at this
    have hle : M₁ ⊔ M₂ ≤ Subgroup.normalizer (N : Set E) :=
      sup_le (hnorm M₁ hconj1) (hnorm M₂ hconj2)
    rw [hyp.gen] at hle
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
  have hNbot := hN N hNnorm hNle
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
  have hzG1 : z ∈ stv β β.xv := MulAction.mem_stabilizer_iff.mpr (hzall z hz β.xv)
  obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 β hzG1
  have haN : ι₁ a ∈ N := ⟨a, (hKmem _).mpr (hzall _ hz), rfl⟩
  rw [hNbot, Subgroup.mem_bot] at haN
  have : a = 1 := M₁.subtype_injective (haN.trans (map_one _).symm)
  rw [this, map_one]

theorem burnsideF4n_four_dvd_card_M1 {p : ℕ} {E : Type} [Group E] [Finite E]
    {M₁ M₂ : Subgroup E}
    (hpar : IsLieParabolics p ⊤ (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) (hp : p = 2)
    (h4 : 4 ∣ Nat.card E) : 4 ∣ Nat.card M₁ := by
  subst hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S, ⟨-, hSp, hSi⟩, hB⟩, -⟩ := hpar
  have hSM : S ≤ M₁ := by
    intro s hs
    have h1 : s ∈ (⊤ : Subgroup E) ⊓ Subgroup.normalizer (S : Set E) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_top s, Subgroup.le_normalizer hs⟩
    rw [← hB] at h1
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h1).2).1
  rw [Subgroup.relIndex_top_right] at hSi
  obtain ⟨n, hn⟩ := hSp.exists_card_eq
  have hmul := Subgroup.card_mul_index S
  have h4S : 4 ∣ Nat.card S := by
    rw [hn]
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · exfalso
      apply hSi
      rw [hn] at hmul
      obtain ⟨k, hk⟩ := h4
      interval_cases n
      · rw [pow_zero, one_mul] at hmul
        exact ⟨2 * k, by omega⟩
      · rw [pow_one] at hmul
        exact ⟨k, by omega⟩
    · calc 4 = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n := pow_dvd_pow 2 hge
  exact dvd_trans h4S (Subgroup.card_dvd_of_le hSM)

theorem burnsideF4n_model_facts
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f ⊤ M₁ M₂) (hκ : κ = .G2d ∨ κ = .Tits) :
    p = 2 ∧ 4 ∣ Nat.card E ∧ IsSimpleGroup E := by
  rcases hκ with rfl | rfl
  · obtain ⟨hp2, -, -⟩ := hyp.model
    obtain ⟨Φ, -, -, -⟩ := burnsideF4nB_ident hyp
    have hcard : Nat.card E = 6048 := (Nat.card_congr Φ.toEquiv).symm.trans card_u33Pres
    refine ⟨hp2, by rw [hcard]; norm_num, ?_⟩
    haveI := isSimpleGroup_u33Pres
    exact MulEquiv.isSimpleGroup Φ.symm
  · obtain ⟨hp2, -, hmodel⟩ := hyp.model
    obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ p f hmodel
    let e' : E ≃* CFSG.Sporadic.Schreier.Tits.titsD := Subgroup.topEquiv.symm.trans e
    have hcard : Nat.card E = 17971200 :=
      (Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.Schreier.Tits.card_titsD
    refine ⟨hp2, by rw [hcard]; norm_num, ?_⟩
    haveI := CFSG.Sporadic.Schreier.Tits.titsD_simple
    exact MulEquiv.isSimpleGroup e'

theorem burnsideF4n_F422Facts_holds :
    burnsideF4n_F422Facts := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ
  haveI : Finite E := hyp.finite
  have hpar := burnsideF4n_parabolics_at hyp
  subst hGp
  obtain ⟨hp2, h4, hsimple⟩ := burnsideF4n_model_facts hyp hκ
  have h4M := burnsideF4n_four_dvd_card_M1 hpar hp2 h4
  refine ⟨by omega, by omega, fun N hN hNle => ?_⟩
  haveI := hsimple
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    obtain ⟨-, hne, -⟩ := hpar
    apply hne
    rw [h] at hNle
    have h1 : M₁ = ⊤ := top_le_iff.mp (hNle.trans inf_le_left)
    have h2 : M₂ = ⊤ := top_le_iff.mp (hNle.trans inf_le_right)
    rw [h1, h2]

theorem burnside_as_F_4_22_of
    (h45 : F_4_5) (h46 : F_4_6) :
    F_4_22 :=
  burnsideF4n_F422_of_facts h45 h46 burnsideF4n_F422Facts_holds

end CFSG.ASVolI
