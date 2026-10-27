module

public import CFSG.Timmesfeld.ARS.BasicRankOne
public import CFSG.Timmesfeld.Bridge.RootStructWTIModule

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {D : Set G}

namespace LineSetting

variable (hL : LineSetting G D)
include hL

section Line

variable {a d : G}

theorem nCore_le_lineN_sup (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) {p : G}
    (hp : p ∈ D) (hpT : p ∈ rootGroup D a ⊔ rootGroup D d) :
    nCore D p ≤ lineN D a d ⊔ (rootGroup D x ⊔ rootGroup D y) := by
  have hclass := hL.hyp.isClass
  have hD := hL.hyp.root
  have hc := hL.closure
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  have hyT' : y ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hyT
  set X := rootGroup D x ⊔ rootGroup D y with hX
  have hMa : nCore D a ≤ lineN D a d ⊔ X := by
    rw [hL.nCore_eq_rootGroup_sup ha hd had hadD hdT hx hax haxD hxT]
    exact sup_le (le_sup_of_le_right le_sup_left) (le_sup_of_le_left le_sup_left)
  have hMd : nCore D d ≤ lineN D a d ⊔ X := by
    rw [hL.nCore_eq_rootGroup_sup hd ha had.symm hdaD haT hy hdy hdyD hyT']
    exact sup_le (le_sup_of_le_right le_sup_right) (le_sup_of_le_left le_sup_right)
  have hXN := hL.sup_rootGroup_le_normalizer_lineN ha hd had hadD hdT hx hax haxD hxT hy hdy
    hdyD hyT
  have hconj : ∀ g ∈ X, ∀ n ∈ lineN D a d ⊔ X, g * n * g⁻¹ ∈ lineN D a d ⊔ X := by
    intro g hg n hn
    have hmap : (lineN D a d ⊔ X).map (MulAut.conj g).toMonoidHom = lineN D a d ⊔ X := by
      rw [Subgroup.map_sup, RankOne.map_conj_eq_self_iff.2 (hXN hg), RankOne.map_conj_of_mem hg]
    rw [← hmap]
    exact RankOne.conj_mem_map_conj g hn
  have hp1 : p ≠ 1 := hD.ne_one hp
  by_cases hpa : p ∈ rootGroup D a
  · rw [hL.nCore_eq_of_mem_rootSet ha
      (((mem_rootGroup_iff_of_rootClosure hD hc ha).1 hpa).resolve_left hp1)]
    exact hMa
  obtain ⟨α, hα, δ, hδ, hpe⟩ := exists_mul_eq_of_mem_line hd had hpT
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hpe
    exact hpa (hpe ▸ hα)
  have hδT : δ ∈ rootSet D d := ((mem_rootGroup_iff_of_rootClosure hD hc hd).1 hδ).resolve_left hδ1
  by_cases hα1 : α = 1
  · rw [hα1, one_mul] at hpe
    rw [hpe, hL.nCore_eq_of_mem_rootSet hd hδT]
    exact hMd
  have hαT : α ∈ rootSet D a := ((mem_rootGroup_iff_of_rootClosure hD hc ha).1 hα).resolve_left hα1
  have haδ : Commute a δ := (commute_of_mem_rootGroup_of_commute hδ ha had.symm).symm
  have hδL : δ ∈ rootGroup D a ⊔ rootGroup D d := Subgroup.mem_sup_right hδ
  have haδD : a * δ ∈ D := by
    refine mem_of_mem_sup_rootGroup hL.hyp hc hL.special ha hd had hadD hdT
      (Subgroup.mul_mem _ (left_mem_line ha) hδL) fun h => ?_
    have hδa : δ ∈ rootGroup D a := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact (rootGroup D a).inv_mem (rootSet_subset_rootGroup D a (mem_rootSet_self ha))
    have hne : rootSet D a ≠ rootSet D d := fun h' => hdT (h' ▸ mem_rootSet_self hd)
    have := rootGroup_inf_eq_bot_of_rootClosure hD hc ha hd hne
    have hmem : δ ∈ rootGroup D a ⊓ rootGroup D d := ⟨hδa, hδ⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hδ1 hmem
  have h4x : orderOf (δ * x) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd hx hδT (mem_rootSet_self hx)
      (hL.orderOf_mul_eq_four_of_collinear ha hd had hadD hdT hx hax hxT)
  obtain ⟨x₁, hx₁, hx₁e⟩ := exists_mem_rootSet_conj_eq_mul hL.hyp hc hL.special hL.commLambda
    ha hδT.1 haδ haδD hx hax haxD h4x hαT
  have hαδ : Commute α δ := commute_of_mem_sup_rootGroup ha hd had (Subgroup.mem_sup_left hα) hδL
  have hpe' : p = x₁ * δ * x₁⁻¹ := by rw [hx₁e, hpe, hαδ.eq]
  have hx₁X : x₁ ∈ X := Subgroup.mem_sup_left (rootSet_subset_rootGroup D x hx₁)
  intro n hn
  have h1 : x₁⁻¹ * n * x₁ ∈ nCore D d := by
    have := conj_mem_nCore_conj hclass hn x₁⁻¹
    rw [hpe', inv_inv, show x₁⁻¹ * (x₁ * δ * x₁⁻¹) * x₁ = δ by group,
      hL.nCore_eq_of_mem_rootSet hd hδT] at this
    exact this
  have := hconj x₁ hx₁X _ (hMd h1)
  rwa [show x₁ * (x₁⁻¹ * n * x₁) * x₁⁻¹ = n by group] at this

theorem closure_normalizesLine_eq (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) :
    Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} =
      lineN D a d ⊔ (rootGroup D x ⊔ rootGroup D y) := by
  have hTI := hL.lineTI ha hd had hadD hdT
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro v ⟨hvD, hvN⟩
    obtain ⟨e, heD, heT, hve⟩ := exists_commute_of_normalizesLine hL.hyp hL.closure hL.special ha
      hd had hadD hdT hvD hvN
    exact hL.nCore_le_lineN_sup ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT heD heT
      (hL.mem_nCore_of_commute heD hvD hve.symm)
  · have hcomm : ∀ {p : G}, p ∈ D → p ∈ rootGroup D a ⊔ rootGroup D d →
        nCore D p ≤ Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} := by
      intro p hp hpT
      rw [hL.nCore_eq_closure hp]
      exact Subgroup.closure_mono fun c ⟨hc, hpc⟩ => ⟨hc, normalizesLine_of_commute hL.hyp
        hL.closure hL.special ha hd had hadD hdT hTI hp hpT hc hpc.symm⟩
    have hMa := hcomm ha (left_mem_line ha)
    have hMd := hcomm hd (right_mem_line hd)
    exact sup_le (sup_le (inf_le_left.trans hMa) (inf_le_left.trans hMd))
      (sup_le ((hL.rootGroup_le_nCore ha hax).trans hMa) ((hL.rootGroup_le_nCore hd hdy).trans hMd))

end Line

end LineSetting

namespace LineSetting

section TypeZero

variable {G : Type} [Group G] {D : Set G} (hL : LineSetting G D)
include hL

variable {a d : G}

theorem exists_mulEquiv_SL2_line (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ e : ℕ, Nat.card (rootGroup D a) = 2 ^ e ∧
      ∃ φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
        ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
          upperUnipotent (GaloisField 2 e) ∧
        ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
          lowerUnipotent (GaloisField 2 e) := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hc := hL.closure
  have hTI := hL.lineTI ha hd had hadD hdT
  have hay : orderOf (a * y) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line' hD hL.lineCentralizerEq ha hd had hadD hdT hTI hy
      hdy hyT
  obtain ⟨hyx, hodd⟩ := opposite_of_not_mem_line hclass hD hc hL.special hL.commLambda
    hL.lineCentralizerEq ha hd had hadD hdT hTI hy hdy hdyD hay hx hax haxD hxT
  have hxd : orderOf (x * d) = 4 :=
    orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha hd had hadD hdT hTI hx hax hxT
  have h1 : OneOpposite D y x := ⟨d, hd, hdy.symm, by rw [← hdy.eq]; exact hdyD, hxd⟩
  have hcardx : Nat.card ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)) =
      Nat.card (rootGroup D a) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      card_rootGroup_eq hclass hD hc ha hx]
  obtain ⟨e, he⟩ := exists_card_rootGroup_eq_two_pow hD ha
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · interval_cases e
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at he
      have : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self ha)
      rw [he, Subgroup.mem_bot] at this
      exact hD.ne_one ha this
    · refine ⟨1, he, ?_⟩
      have hM := moufangPair_of_oneOpposite hL.hyp hc hL.special hL.commLambda hy hx hyx hodd h1
      have hR := isElemAbRankOne_of_moufangPair hclass hD hc hx hy (fun h => hyx h.symm)
        ((orderOf_mul_comm_eq x y) ▸ hodd) hM
      exact ARS.ElemAbRankOne.exists_mulEquiv_SL2_two hR (by rw [hcardx, he, pow_one])
  · have hq4 : 4 ≤ Nat.card (rootGroup D y) := by
      rw [card_rootGroup_eq hclass hD hc ha hy, he]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    obtain ⟨n, -, hn, φ, hφx, hφy⟩ := exists_mulEquiv_SL2_of_oneOpposite hL.hyp hc hL.special
      hL.commLambda hy hx hyx hodd h1 hq4
    exact ⟨n, by rw [← hcardx, hn], φ, hφx, hφy⟩

end TypeZero

end LineSetting

theorem rootLinesModuleStep :
    ∀ (G : Type) [Group G] (D : Set G), LineSetting G D →
      ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      ∀ x ∈ D, Commute a x → a * x ∈ D → x ∉ rootGroup D a ⊔ rootGroup D d →
      ∀ y ∈ D, Commute d y → d * y ∈ D → y ∉ rootGroup D a ⊔ rootGroup D d →
        (nCore D a = rootGroup D x ⊔ (nCore D a ⊓ Subgroup.centralizer {d}) ∧
          rootGroup D x ⊓ Subgroup.centralizer {d} = ⊥) ∧
        ∃ e : ℕ, Nat.card (rootGroup D a) = 2 ^ e ∧
        ∃ φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
          ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
            upperUnipotent (GaloisField 2 e) ∧
          ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
            lowerUnipotent (GaloisField 2 e) ∧
          (∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ n ∈ lineN D a d, g * n * g⁻¹ ∈ lineN D a d) ∧
          (∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ n ∈ lineN₀ D a d,
            g * n * g⁻¹ ∈ lineN₀ D a d) ∧
          lineN₀ D a d ≤ lineN D a d ∧
          (∀ n ∈ lineN D a d, ∀ m ∈ lineN₀ D a d, n * m * n⁻¹ ∈ lineN₀ D a d) ∧
          (∀ n ∈ lineN D a d, ∀ n' ∈ lineN D a d, n * n' * n⁻¹ * n'⁻¹ ∈ lineN₀ D a d) ∧
          (∃ k : ℕ, ∃ Nf : Fin k → Subgroup G, ∃ θ : Fin k → (Fin 2 → GaloisField 2 e) → G,
            (∀ i, lineN₀ D a d ≤ Nf i ∧
              Higman.IsNaturalQuotient φ (Nf i) (lineN₀ D a d) (θ i)) ∧
            (∀ i, ∀ s : GaloisField 2 e,
              θ i ![s, 0] ∈ nCore D a ⊓ Subgroup.centralizer {d} ∧
                θ i ![0, s] ∈ nCore D d ⊓ Subgroup.centralizer {a}) ∧
            lineN₀ D a d ⊔ ⨆ i, Nf i = lineN D a d ∧
            Nat.card (lineN D a d) =
              Nat.card (lineN₀ D a d) * Nat.card (rootGroup D a) ^ (2 * k) ∧
            Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) =
              Nat.card (lineN₀ D a d) * Nat.card (rootGroup D a) ^ k ∧
            Nat.card ↥(nCore D d ⊓ Subgroup.centralizer {a}) =
              Nat.card (lineN₀ D a d) * Nat.card (rootGroup D a) ^ k) ∧
          Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} =
            lineN D a d ⊔ (rootGroup D x ⊔ rootGroup D y) := by
  intro G _ D hL a ha d hd had hadD hdT x hx hax haxD hxT y hy hdy hdyD hyT
  have := hL.hyp.finite
  have hH := hL.quotModHyp ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  obtain ⟨e, he, φ, hφx, hφy⟩ :=
    hL.exists_mulEquiv_SL2_line ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  have hq := hL.card_rootGroup_eq_card_field ha hx φ hφx
  obtain ⟨k, Nf, θ, hNf, hθ, hsup, hN, hA, hB⟩ :=
    hL.exists_natural_lineN ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT φ hφx hφy
  refine ⟨⟨hL.nCore_eq_rootGroup_sup ha hd had hadD hdT hx hax haxD hxT,
    hL.rootGroup_inf_centralizer_eq_bot ha hd had hadD hdT hx hax hxT⟩, e, he, φ, hφx, hφy,
    hH.conj, hH.conj₀, hH.le, fun n hn m hm => hH.conj_mem hn hm, hH.comm,
    ⟨k, Nf, θ, hNf, hθ, hsup, by rw [hN, hq], by rw [hA, hq], by rw [hB, hq]⟩,
    hL.closure_normalizesLine_eq ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT⟩

end CFSG.Timmesfeld.Bridge
