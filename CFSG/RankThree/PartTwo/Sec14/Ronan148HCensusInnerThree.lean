module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusCover

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

section Row

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.exists_innerCfg (hcfg : OLCfg P L Q) (hZL : Subgroup.center L = ⊥)
    (hPI : P ≤ innerSub L) (hQI : Q ≤ innerSub L) : ∃ B V : Subgroup L, InnerCfg B V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCP : IsPGroup 3 (Subgroup.centralizer (P : Set X)) :=
    ThreeGroup.isPGroup_centralizer hcfg.perf hcfg.triple hcfg.e27
  have hPpg : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hcfg.e27.1.2 x x.2)⟩
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcfg.e27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZP : Subgroup.center X ≤ P := center_le_of_isE27 hcfg.perf hcfg.triple hcfg.e27
  have hQ3 : ¬ 3 ∣ Nat.card Q := by rw [hcfg.klein.card_four]; norm_num
  set I := innerSub L with hIdef
  set φ := innerHom hZL with hφ
  set P' := P.subgroupOf I with hP'
  set Q' := Q.subgroupOf I with hQ'
  set B := P'.map φ with hB
  set V := Q'.map φ with hV
  have hker : ∀ x : I, φ x = 1 ↔ ∀ l ∈ L, (x : X) * l = l * x := innerHom_eq_one_iff hZL
  have hCQ : Q ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
    have hPn : P ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hcfg.normQ hx,
        mem_normalizer_centralizer (hcfg.normL hx)⟩
    rcases eq_bot_or_eq_of_le_kleinFour hcfg.klein inf_le_left hPn hCP with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hcfg.Qnc
  have hQinj : Function.Injective (φ.comp Q'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : ((y : I) : X) ∈ Q ⊓ Subgroup.centralizer (L : Set X) := by
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      exact ((hker y).mp hy l hl).symm
    rw [hCQ, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hcfgI : InnerCfg B V := by
    refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hux, ← hvy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hPab _ hu _ hv)
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, show u ^ 3 = 1 from Subtype.ext (hcfg.e27.1.2 _ hu), map_one]
    ·
      set ψ := φ.comp P'.subtype with hψ
      have hrange : ψ.range = B := range_comp_subtype φ P'
      have hP'card : Nat.card P' = 27 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPI).toEquiv, hcfg.e27.2]
      have hkercard : Nat.card ψ.ker = 3 := by
        have hmap : ψ.ker.map (I.subtype.comp P'.subtype) = Subgroup.center X := by
          apply le_antisymm
          · rintro _ ⟨x, hx, rfl⟩
            exact hcfg.cent _ x.2 ((hker (x : I)).mp hx)
          · intro z hz
            exact ⟨⟨⟨z, hPI (hZP hz)⟩, hZP hz⟩, (MonoidHom.mem_ker).mpr
              ((hker _).mpr fun l _ => ((Subgroup.mem_center_iff.mp hz) l).symm), rfl⟩
        have hinj : Function.Injective (I.subtype.comp P'.subtype) := fun a b h =>
          P'.subtype_injective (I.subtype_injective h)
        rw [← Subgroup.card_map_of_injective hinj, hmap, hcfg.triple.1]
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hP'card,
        hkercard] at h
      omega
    ·
      have e' : ↥Q' ≃* ↥V := by
        rw [hV, ← range_comp_subtype φ Q']
        exact MonoidHom.ofInjective hQinj
      have eQ : ↥Q' ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQI
      exact ⟨by rw [← Nat.card_congr e'.toEquiv, Nat.card_congr eQ.toEquiv]; exact hcfg.klein.card_four,
        by rw [← Monoid.exponent_eq_of_mulEquiv e', Monoid.exponent_eq_of_mulEquiv eQ];
           exact hcfg.klein.exponent_two⟩
    ·
      refine le_normalizer_of_conj_mem' fun b hb v hv => ?_
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨y, hy, rfl⟩ := hv
      refine ⟨x * y * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((x : I) : X) * (y : X) * ((x : I) : X)⁻¹ ∈ Q
      exact (Subgroup.mem_normalizer_iff.mp (hcfg.normQ hx) _).mp hy
    ·
      obtain ⟨p₀, hp₀, hp₀z, hQp₀⟩ := hcfg.pt
      set x₀ : I := ⟨p₀, hPI hp₀⟩ with hx₀
      refine ⟨φ x₀, ⟨x₀, hp₀, rfl⟩, fun h => hp₀z (hcfg.cent p₀ hp₀ ((hker x₀).mp h)), ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hQp₀ hy)
    ·
      intro hBV
      have hPQ : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x := by
        intro x hx y hy
        set x' : I := ⟨x, hPI hx⟩
        set y' : I := ⟨y, hQI hy⟩
        have hc : φ x' * φ y' = φ y' * φ x' :=
          (Subgroup.mem_centralizer_iff.mp (hBV ⟨x', hx, rfl⟩) (φ y') ⟨y', hy, rfl⟩).symm
        have hq : x' * y' * x'⁻¹ * y'⁻¹ ∈ Q' := by
          show x * y * x⁻¹ * y⁻¹ ∈ Q
          exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hcfg.normQ hx) y).mp hy)
            (Subgroup.inv_mem _ hy)
        have h1 : (φ.comp Q'.subtype) ⟨_, hq⟩ = 1 := by
          simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
          rw [hc]; group
        have h2 := congrArg Subtype.val (congrArg Subtype.val (hQinj (h1.trans (map_one _).symm)))
        simp only [OneMemClass.coe_one, Subgroup.coe_mul, Subgroup.coe_inv] at h2
        calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
          _ = y * x := by rw [h2, one_mul]
      have hQC : Q ≤ Q ⊓ Subgroup.centralizer (P : Set X) := fun y hy =>
        ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => hPQ x hx y hy⟩
      rw [inf_eq_bot_of_not_dvd hCP hQ3, le_bot_iff] at hQC
      have := hcfg.klein.card_four
      rw [hQC, Subgroup.card_bot] at this
      omega
    ·
      intro R hR
      set RX := R.map L.subtype with hRX
      have hRX3 : ¬ 3 ∣ Nat.card RX := by
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        exact not_dvd_of_isPiSubgroup hR.2.1
      have hPR : P ≤ Subgroup.normalizer (RX : Set X) := by
        refine le_normalizer_of_conj_mem' fun x hx r hr => ?_
        obtain ⟨r', hr', rfl⟩ := hr
        set x' : I := ⟨x, hPI hx⟩
        have h1 := innerHom_spec hZL x' r'
        have h2 : φ x' * r' * (φ x')⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hR.2.2 ⟨x', hx, rfl⟩) r').mp hr'
        refine ⟨_, h2, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1.symm
      have hRQ := hcfg.inv RX ((Subgroup.map_subtype_le R).trans le_sup_left)
        ⟨le_top, isPiSubgroup_of_not_dvd hRX3, hPR⟩
      intro r hr
      have hrQ : (r : X) ∈ Q := hRQ ⟨r, hr, rfl⟩
      refine ⟨⟨r, hQI hrQ⟩, hrQ, ?_⟩
      exact innerHom_of_mem hZL ⟨r, hQI hrQ⟩ r.2
  exact ⟨B, V, hcfgI⟩


theorem olRow_of_innerThree (S : Type) [Group S] [IsSimpleGroup S] (hinn : InnerThree S)
    (hno : ∀ B V : Subgroup S, ¬ InnerCfg B V) : OLRow (fun T _ => Nonempty (T ≃* S)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  have hZL : Subgroup.center L = ⊥ :=
    Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hcfg.isQuasisimple e
  obtain ⟨hPI, hQI⟩ := hcfg.le_innerSub (hinn.of_mulEquiv e)
  obtain ⟨B, V, hc⟩ := hcfg.exists_innerCfg hZL hPI hQI
  exact hno _ _ (hc.map e)

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
