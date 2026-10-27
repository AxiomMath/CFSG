module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DE
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DG
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DH
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem coords_ch615 (c : Cx615B G T M L V H n) :
    oTwoUpper H ≤ thompsonJ H ∧
    autI c.hU (baum T) = autI c.hU (thompsonJ T) ∧
    IsSylowTwoOf (autI c.hU (thompsonJ T)) (autI c.hU (thompsonJ H)) ∧
    IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T) ∧
    ((∃ ψ₁ : SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU), Function.Injective ψ₁ ∧
        ψ₁.range = autI c.hU (thompsonJ H)) ∨
     (∃ ψ : SL22 × SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU), Function.Injective ψ ∧
        ψ.range = autI c.hU (thompsonJ H) ∧ ∃ t : ↥H, (t : G) ∈ T ∧
        (∀ u : SL22, ∃ v : SL22, c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹ = ψ (1, v)) ∧
        (∀ v : SL22, ∃ u : SL22, ψ (1, v) = c.cvH t * ψ (u, 1) * (c.cvH t)⁻¹))) := by
  classical
  obtain ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans, htype, -, -, h2, -⟩ := c.e23
  have hnat := c.s3 I hcard hJeq htype
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hTH : T ≤ H := c.hH.1.1
  have hOJ : oTwoUpper H ≤ thompsonJ H := by rw [← twoResidual_eq_oTwoUpper']; exact hKJ
  obtain ⟨hb, hsyl, hsylB, -⟩ := h2 fun L hL => ⟨1, hnat L hL⟩
  rw [twoResidual_eq_oTwoUpper'] at hsylB
  refine ⟨hOJ, hb, hsyl, hsylB, ?_⟩
  rcases hcard with h1 | h2'
  · obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp h1
    have hBL : autI c.hU (thompsonJ H) = L₁ := by rw [hJeq]; simp
    obtain ⟨ψ₁, hψ₁, hr₁⟩ :=
      exists_hom_of_isL2Natural_ch615 (hnat L₁ (Finset.mem_singleton_self _))
    exact Or.inl ⟨ψ₁, hψ₁, hr₁.trans hBL.symm⟩
  · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2'
    have hm₁ : L₁ ∈ ({L₁, L₂} : Finset _) := Finset.mem_insert_self _ _
    have hm₂ : L₂ ∈ ({L₁, L₂} : Finset _) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hBL : autI c.hU (thompsonJ H) = L₁ ⊔ L₂ := by
      rw [hJeq, Finset.iSup_insert, Finset.iSup_singleton]
    have hdisj : L₁ ⊓ L₂ = ⊥ := by
      refine le_bot_iff.mp (le_trans (inf_le_inf_left _ ?_) (hind L₁ hm₁).le)
      exact le_iSup₂_of_le (f := fun L' _ => ⨆ (_ : L' ≠ L₁), L') L₂ hm₂
        (le_iSup_of_le hne.symm le_rfl)
    obtain ⟨ψ₁, hψ₁, hr₁⟩ := exists_hom_of_isL2Natural_ch615 (hnat L₁ hm₁)
    obtain ⟨ψ₂, hψ₂, hr₂⟩ := exists_hom_of_isL2Natural_ch615 (hnat L₂ hm₂)
    obtain ⟨ψ, hψ, hr, hψl, hψr⟩ := exists_hom_two_ch615 hψ₁ hψ₂ hr₁ hr₂
      (hcomm L₁ hm₁ L₂ hm₂ hne) hdisj
    obtain ⟨tc, htc, htL⟩ := htrans L₁ hm₁ L₂ hm₂
    rw [autI_eq_map_convHom c.hU hHN hTH] at htc
    obtain ⟨t, ht, htt⟩ := htc
    have htt' : c.cvH t = tc := htt
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    refine Or.inr ⟨ψ, hψ, hr.trans hBL.symm, t, ht, fun u => ?_, fun v => ?_⟩
    · have hmem : tc * ψ (u, 1) * tc⁻¹ ∈ L₂ := by
        rw [← htL, B1.mem_conjAut, hψl, ← hr₁]
        exact ⟨u, by group⟩
      rw [← hr₂] at hmem
      obtain ⟨v, hv⟩ := hmem
      exact ⟨v, by rw [htt', hψr, hv]⟩
    · have hmem : ψ (1, v) ∈ B1.conjAut tc L₁ := by
        rw [htL, hψr, ← hr₂]; exact ⟨v, rfl⟩
      rw [B1.mem_conjAut, ← hr₁] at hmem
      obtain ⟨u, hu⟩ := hmem
      refine ⟨u, ?_⟩
      rw [htt', hψl, hu]
      group

end Cx615B



abbrev s2615 (T L H : Subgroup G) : Subgroup G := baum T ⊔ pCoreOf 2 (borelL T L ⊔ H)

namespace Cx615C

theorem s2_facts_ch615 (hR1 : L2RankOneSylowFact) (c : Cx615C G T M L V H n) :
    s2615 T L H ≤ T ∧ T ⊓ L ≤ s2615 T L H ∧
    borelL T L ≤ Subgroup.normalizer (s2615 T L H : Set G) ∧
    T ≤ Subgroup.normalizer (s2615 T L H : Set G) ∧
    autI c.hU (s2615 T L H) = autI c.hU (thompsonJ T) ∧ CharTwo (L ⊔ s2615 T L H) ∧
    CharTwo (borelL T L ⊔ H) := by
  have h := c.hyp
  set X := borelL T L ⊔ H with hX
  have hTH : T ≤ H := c.hH.1.1
  have hTX : T ≤ X := hTH.trans le_sup_right
  have hQT : pCoreOf 2 X ≤ T := by rw [c.QX]; exact inf_le_left
  have hbT : baum T ≤ T := inf_le_left
  have hS2T : s2615 T L H ≤ T := sup_le hbT hQT
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hnS2 : ∀ g : G, g ∈ Subgroup.normalizer (baum T : Set G) → g ∈ X →
      g ∈ Subgroup.normalizer (s2615 T L H : Set G) := by
    intro g h1 hgX
    have h2 := le_normalizer_pCoreOf 2 X hgX
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hTS2 : T ≤ Subgroup.normalizer (s2615 T L H : Set G) := fun t ht =>
    hnS2 t (normalizer_le_normalizer_baum T (Subgroup.le_normalizer ht)) (hTX ht)
  refine ⟨hS2T, (c.inf_le_baum_ch615 hR1).trans le_sup_left, fun b hb =>
    hnS2 b (c.borelL_le_normalizer_baum_ch615 hb) (Subgroup.mem_sup_left hb), hTS2, ?_, ?_, ?_⟩
  ·
    have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
    have hQC : pCoreOf 2 X ≤ Subgroup.centralizer (Cx615.UH T H : Set G) := by
      rw [c.QX]
      exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        (conjClosure_mono le_rfl le_sup_right)))
    obtain ⟨-, hb, -⟩ := c.coords_ch615
    rw [autI_eq_map_convHom c.hU hHN (hS2T.trans hTH),
      Subgroup.subgroupOf_sup (hbT.trans hTH) (hQT.trans hTH), Subgroup.map_sup,
      ← autI_eq_map_convHom c.hU hHN (hbT.trans hTH), ← autI_eq_map_convHom c.hU hHN
        (hQT.trans hTH), autI_eq_bot_of_le_centralizer c.hU hQC, sup_bot_eq, hb]
  ·
    have hLT : CharTwo (L ⊔ T) := charTwo_of_inH' h.qtke h.sylow
      ⟨le_sup_right, fun h0 => h.module.2.2 (by
        have hV : V ≤ pCoreOf 2 (L ⊔ T) := by
          rw [← h.centralizer_eq]
          exact le_inf c.V_facts.2.2 (fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
            (B2F.isElemAbelian_comm c.V_facts.1 hw hv))
        rw [h0, le_bot_iff] at hV
        rw [hV]
        exact Subgroup.commutator_bot_left L)⟩
    have hle : L ⊔ s2615 T L H ≤ L ⊔ T := sup_le_sup le_rfl hS2T
    refine CharTwo.of_normal hLT hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_)
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · refine mem_normalizer_of_conj_mem_ch6 fun y hy => ?_
      have hy' : y ∈ ((L ⊔ s2615 T L H : Subgroup G) : Set G) := hy
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ (hS2T.trans hTL)] at hy'
      obtain ⟨a, ha, s, hs, rfl⟩ := hy'
      have hls : l * s * l⁻¹ * s⁻¹ ∈ L := by
        have h1 : s * l⁻¹ * s⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hTL (hS2T hs)) _).mp (L.inv_mem hl)
        have e1 : l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) := by group
        rw [e1]
        exact L.mul_mem hl h1
      have e1 : l * (a * s) * l⁻¹ = (l * a * l⁻¹) * (l * s * l⁻¹ * s⁻¹) * s := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
        (L.mul_mem (L.mul_mem hl ha) (L.inv_mem hl))) (Subgroup.mem_sup_left hls))
        (Subgroup.mem_sup_right hs)
    · have h1 := hTL ht
      have h2 := hTS2 ht
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
      rw [Subgroup.map_sup, h1, h2]
  · exact charTwo_of_inH' h.qtke h.sylow ⟨hTX, c.X_O2⟩

end Cx615C

namespace Cx615C

theorem exists_odd_ch615 (c : Cx615C G T M L V H n) :
    ∃ k ∈ oTwoUpper H, Odd (orderOf k) ∧
      k ∉ Subgroup.centralizer (Cx615.UH T H : Set G) := by
  by_contra hall
  have h := c.hyp
  have hTH : T ≤ H := c.hH.1.1
  have hKC : oTwoUpper H ≤ Subgroup.centralizer (Cx615.UH T H : Set G) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    by_contra hxC
    exact hall ⟨x, mem_oTwoUpper_of_odd hx.1 hx.2, hx.2, hxC⟩
  have hKO : oTwoUpper H ≤ T :=
    (le_inf (oTwoUpper_le H) hKC).trans (c.cent.le.trans
      (F7.isSylowTwoOf_pCoreOf_le c.toCx615.isSylowTwoOf))
  apply c.hH.2.1
  rw [← sup_twoResidual_eq c.toCx615.isSylowTwoOf, twoResidual_eq_oTwoUpper']
  exact sup_le h.T_le (hKO.trans h.T_le)

theorem oTwoUpper_not_le_ch615 (c : Cx615C G T M L V H n) : ¬ oTwoUpper H ≤ M := by
  intro hle
  apply c.hH.2.1
  rw [← sup_twoResidual_eq c.toCx615.isSylowTwoOf, twoResidual_eq_oTwoUpper']
  exact sup_le c.hyp.T_le hle

end Cx615C
namespace Cx615C

theorem exists_s3_one_ch615 (hR1 : L2RankOneSylowFact) (c : Cx615C G T M L V H n)
    (hK : borelL T L ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    {ψ₁ : SL22 →* MulAut (IntMod (Cx615.UH T H) c.hU)} (hψ₁ : Function.Injective ψ₁)
    (hr₁ : ψ₁.range = autI c.hU (thompsonJ H)) :
    ∃ S P₁ : Subgroup G, S ≤ T ∧ T ⊓ L ≤ S ∧ S ≤ Subgroup.normalizer (P₁ : Set G) ∧
      borelL T L ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (S ⊓ P₁) P₁ ∧
      Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) ∧ CharTwo (L ⊔ S) ∧
      CharTwo (P₁ ⊔ S ⊔ borelL T L) := by
  classical
  have h := c.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set S2 := s2615 T L H with hS2def
  set P₁ := K ⊔ S2 with hP₁def
  obtain ⟨hS2T, hTLS, hBS2, hTS2, hautS2, hcL, hcX⟩ := c.s2_facts_ch615 hR1
  obtain ⟨hOJ, -, hsyl, hsylB, -⟩ := c.coords_ch615
  have hTH : T ≤ H := c.hH.1.1
  have hKH : K ≤ H := oTwoUpper_le H
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hS2H : S2 ≤ H := hS2T.trans hTH
  have hP₁H : P₁ ≤ H := sup_le hKH hS2H
  have hS2K : S2 ≤ Subgroup.normalizer (K : Set G) := hS2H.trans hHK
  have hsup : ∀ g : G, g ∈ Subgroup.normalizer (K : Set G) →
      g ∈ Subgroup.normalizer (S2 : Set G) → g ∈ Subgroup.normalizer (P₁ : Set G) := by
    intro g h1 h2
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  refine ⟨S2, P₁, hS2T, hTLS, fun s hs => hsup s (hS2K hs) (Subgroup.le_normalizer hs),
    fun b hb => hsup b (hK hb) (hBS2 hb), fun hle => c.oTwoUpper_not_le_ch615
      (le_sup_left.trans hle), ?_, ?_, hcL, ?_⟩
  · rw [inf_of_le_left le_sup_right]
    exact isSylowTwoOf_sup_ch615 (le_sup_left : baum T ≤ S2) (h.sylow.1.to_le hS2T) hS2K hsylB
  ·
    have hP₁N : P₁ ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := hP₁H.trans hHN
    set φ := convHom c.hU P₁ hP₁N with hφ
    have hrange : φ.range ≤ ψ₁.range := by
      rw [range_convHom, hr₁, autI_eq_map_convHom c.hU hHN hP₁H,
        Subgroup.subgroupOf_sup hKH hS2H, Subgroup.map_sup,
        ← autI_eq_map_convHom c.hU hHN hKH, ← autI_eq_map_convHom c.hU hHN hS2H, hautS2]
      exact sup_le (autI_mono c.hU hOJ) hsyl.1
    set θ : SL22 ≃* ↥ψ₁.range := MonoidHom.ofInjective hψ₁ with hθ
    set ρ : ↥P₁ →* SL22 :=
      θ.symm.toMonoidHom.comp (φ.codRestrict ψ₁.range fun x => hrange ⟨x, rfl⟩) with hρ
    have hψρ : ∀ x : ↥P₁, ψ₁ (ρ x) = φ x := by
      intro x
      have e1 : θ (ρ x) = ⟨φ x, hrange ⟨x, rfl⟩⟩ := by
        rw [hρ]
        simp
      have := congrArg Subtype.val e1
      rw [hθ, MonoidHom.ofInjective_apply] at this
      exact this
    have hρ1 : ∀ x : ↥P₁, ρ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (Cx615.UH T H : Set G) := by
      intro x
      rw [← hψ₁.eq_iff, map_one, hψρ, hφ, convHom_apply, convI_eq_one_iff]
    have hker2 : IsPGroup 2 ρ.ker := by
      rintro ⟨x, hx⟩
      have hxC := (hρ1 x).mp hx
      have hxO : (x : G) ∈ pCoreOf 2 H := c.cent.le ⟨hP₁H x.2, hxC⟩
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨x, hxO⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hk
    have hρs : Function.Surjective ρ := by
      rw [← MonoidHom.range_eq_top]
      obtain ⟨k, hkK, hkodd, hkC⟩ := c.exists_odd_ch615
      set k' : ↥P₁ := ⟨k, Subgroup.mem_sup_left hkK⟩
      have hk1 : ρ k' ≠ 1 := fun h1 => hkC ((hρ1 k').mp h1)
      have hkodd' : Odd (orderOf (ρ k')) := by
        refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ρ k')
        rw [Subgroup.orderOf_mk]
        exact hkodd
      have hk3 : ρ k' ^ 3 = 1 := by
        rcases sq_or_cube_sl22 (ρ k') with h2 | h3
        · exfalso
          apply hk1
          have hd := orderOf_dvd_of_pow_eq_one h2
          exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
            (Nat.coprime_two_right.mpr hkodd') hd)
        · exact h3
      have hJ6 : Nat.card (autI c.hU (thompsonJ H)) = 6 := by
        rw [← hr₁, ← card_sl22]
        exact Nat.card_congr θ.toEquiv.symm
      obtain ⟨j, hjJ, hjC⟩ : ∃ j ∈ thompsonJ T,
          j ∉ Subgroup.centralizer (Cx615.UH T H : Set G) := by
        by_contra hall
        have hb : autI c.hU (thompsonJ T) = ⊥ := autI_eq_bot_of_le_centralizer c.hU
          fun j hj => by
            by_contra hjC
            exact hall ⟨j, hj, hjC⟩
        have h2 := hsyl.2.2
        rw [hb] at h2
        apply h2
        show 2 ∣ (⊥ : Subgroup (MulAut (IntMod (Cx615.UH T H) c.hU))).relIndex
          (autI c.hU (thompsonJ H))
        rw [Subgroup.relIndex_bot_left, hJ6]
        norm_num
      have hjS2 : j ∈ S2 :=
        Subgroup.mem_sup_left ((thompsonJ_le_baum_ch615 T) hjJ)
      set j' : ↥P₁ := ⟨j, Subgroup.mem_sup_right hjS2⟩
      have hj1 : ρ j' ≠ 1 := fun h1 => hjC ((hρ1 j').mp h1)
      have hj2 : ρ j' ^ 2 = 1 := by
        obtain ⟨e, he⟩ := h.sylow.1 ⟨j, hS2T hjS2⟩
        have he' : ρ j' ^ 2 ^ e = 1 := by
          rw [← map_pow]
          have : j' ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
          rw [this, map_one]
        rcases sq_or_cube_sl22 (ρ j') with h2 | h3
        · exact h2
        · exfalso
          apply hj1
          have hcop : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right e (by norm_num)
          exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3) hcop)
            (orderOf_dvd_of_pow_eq_one he'))
      exact eq_top_sl22 ⟨j', rfl⟩ hj1 hj2 ⟨k', rfl⟩ hk1 hk3
    exact nonempty_oTwoQuot_ch615 ρ hρs hker2
  ·
    refine charTwo_of_le_ch615 (P := borelL T L ⊔ H) ?_ hcX ?_
    · exact sup_le (sup_le (hP₁H.trans le_sup_right) (hS2H.trans le_sup_right)) le_sup_left
    · exact (le_sup_right : pCoreOf 2 (borelL T L ⊔ H) ≤ S2).trans (le_sup_right.trans
        le_sup_left)

end Cx615C

end CFSG.Quasithin.H13
