module

public import CFSG.Quasithin.Vol2.Ch11SecD557Q
public import CFSG.Quasithin.Vol2.Ch11SecD557M
public import CFSG.Quasithin.Vol2.Ch11SecD557P
public import CFSG.Quasithin.Vol2.Ch11SecDFacts7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

theorem obl11_5_7SL3Small_of (hF1 : FactCase1NormL1) (hF2 : FactCase1GL8) (hTI : PointsTIFact)
    (hG2 : SecA.FactG2DerivedOrder) (hNat : NatV3Fact) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) : Obl11_5_7SL3Small := by
  intro G _ _ T L I n V₁ x y hconf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hV₁, hSL3, hU, hx, hy, hV, -, hS, hSc, hSs, hSV, hUL, hCS⟩ := hconf
  have hyp := almostSpecialL3Hyp_of_kindSL3 hG2 hNat h1102 h1110 h1141 h hV₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := ⟨hyp, D⟩
  set G₁ := Subgroup.normalizer (V₁ : Set G) with hG₁
  set U := conjClosure (fsuV T I) G₁ with hUdef
  set K := KOf L V₁ V₁ with hKdef
  set L₁ := LOf L V₁ with hL₁def
  have hTN : T ≤ G₁ := SecA.IsVi.le_normalizer hV₁
  have hKG₁ : K ≤ G₁ := kOf_le_normalizer (lOf_le_normalizer L V₁)
  have hG₁U : G₁ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hlt : L₁ < K := lt_of_le_of_ne (le_conjClosure _ _) (Ne.symm hK)
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := exists_isCartanX h
  obtain ⟨K', hLK', hK', hNK', -, hcase⟩ :=
    h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
  have hKK' : K = K' := kOf_eq_of_cComp hLK' hK' hNK' (lOf_ne_bot h1110 h hV₁)
  have hn2 : n = 2 := by
    rcases hcase with heq | ⟨-, hn, -⟩
    · exact absurd (hKK'.trans heq.symm) hK
    · exact hn
  have hcase1 : Case11_1_2One K := by
    rcases (h1141 G T L I n V₁ X h hV₁ hX).2.1 _
      (kOf_cComp_centralizer hTI h1102 h1110 h1112 h1141 h1143 h hV₁) hlt with h1 | h2
    · exact h1
    · exact (h2.2 (isSL3_four h1102 h hSL3 hn2)).elim
  have hlist : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    have hsylN : QuasithinUnique.IsSylowTwoOf (T ⊓ G₁) G₁ := by
      rw [inf_eq_left.mpr hTN]
      exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
    obtain ⟨K'', hLK'', hK'', hNK'', hcase''⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
      (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsylN⟩)
    have hKK'' : K = K'' := kOf_eq_of_cComp hLK'' hK'' hNK'' (lOf_ne_bot h1110 h hV₁)
    rw [← hKK''] at hcase''
    rcases hcase'' with heq | h2 | h3
    · exact absurd heq.symm hlt.ne'
    · exact Or.inl h2
    · exact Or.inr h3
  have hKperf : ⁅K, K⁆ = K := conjClosure_perfect (perfectCore_perfect _)
  have hL₁SL2 := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  obtain ⟨h5one, h5two, h5three⟩ := stmt11_5_5_normalizer h1110 h1154 h1155 h hV₁ hSL3
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁ := fun a ha b hb =>
    h5two (Subgroup.commutator_mem_commutator ha (h5one hb))
  have hUsq : ∀ a ∈ U, a ^ 2 ∈ V₁ := fun a ha => h5three (sq_mem_frattini St.isPGroup_U ha)
  set Zc := U ⊓ Subgroup.centralizer (U : Set G) with hZcdef
  have hZeq : Zc = V₁ ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) :=
    le_antisymm (center_le St hSc hSV hUL hCS) (le_center St hSc hUL hCS)
  have hV₁S : V₁ ≤ pCoreOf 2 (L ⊔ U) :=
    St.hyp.base.le_V.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_conjClosure _ _).trans le_sup_right) St.LU_le_normV St.isPGroup_V)
  have hZS : Zc ≤ pCoreOf 2 (L ⊔ U) := hZeq ▸ sup_le hV₁S hCS
  have hcardZ : Nat.card ↥Zc = 2 ^ n * Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) := by
    have hinf : V₁ ⊓ (U ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : z ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨St.hyp.base.le_V hz.1, hz.2.2⟩
      rwa [inf_centralizer_eq_bot_of_natData St.D] at h1
    have hV₁card : Nat.card ↥V₁ = 2 ^ n := by
      have h1 := SecA.IsVi.relIndex_eq hV₁
      rw [inf_centralizer_eq_bot_of_natData St.D, Subgroup.relIndex_bot_left, mul_one] at h1
      exact h1
    rw [hZeq, card_sup_of_commute (fun a ha b hb => hSc a (hV₁S ha) b (hCS hb)) hinf, hV₁card]
  have hcardU := card_U St hx hy hV hS hSc hSV hCS
  have hrel : Zc.relIndex U = 2 ^ 8 := by
    have h1 := card_eq_mul_relIndex_le (inf_le_left : Zc ≤ U)
    rw [hcardU, hcardZ, hn2] at h1
    have hpos : 0 < 2 ^ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.mul_pos (by norm_num) Nat.card_pos
    have h2 : 2 ^ (5 * 2) * Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) =
        (2 ^ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G))) * 2 ^ 8 := by ring
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hZnorm : G₁ ≤ Subgroup.normalizer (Zc : Set G) := fun g hg =>
    mem_normalizer_inf_centralizer (hG₁U hg)
  have hKC : K ≤ Subgroup.centralizer (Zc : Set G) := by
    have hL₁Z : L₁ ≤ Subgroup.centralizer (Zc : Set G) := by
      rw [Subgroup.le_centralizer_iff, hZeq]
      refine sup_le ?_ fun c hc => Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_iff.mp hc.2 l (((perfectCore_le _).trans inf_le_left) hl))
      exact Subgroup.le_centralizer_iff.mp ((le_conjClosure _ _).trans
        (kOf_le_centralizer hTI h1102 h1141 h1143 h hV₁))
    refine conjClosure_le fun g hg l hl => Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : g⁻¹ * z * g ∈ Zc := by
      have := (Subgroup.mem_normalizer_iff.mp (hZnorm (Subgroup.inv_mem _ hg)) z).mp hz
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hL₁Z hl) _ hz'
    calc z * (g * l * g⁻¹) = g * ((g⁻¹ * z * g) * l) * g⁻¹ := by group
      _ = g * (l * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
      _ = g * l * g⁻¹ * z := by group
  have hconjC : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ z ∈ Subgroup.centralizer (U : Set G),
      g * z * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro g hg z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hz _ hu'
    calc u * (g * z * g⁻¹) = g * ((g⁻¹ * u * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * u := by group
  have hCK : K ⊓ Subgroup.centralizer (U : Set G) ≤ sectionCentralizer K (pCoreOf 2 K) := by
    refine hF1 G K L₁ _ n hlist hcase1 hKperf (le_conjClosure _ _) (perfectCore_perfect _)
      hL₁SL2 inf_le_left (fun k hk => A4.mem_normalizer_of_conj_mem fun z hz =>
        ⟨K.mul_mem (K.mul_mem hk hz.1) (K.inv_mem hk), hconjC k (hG₁U (hKG₁ hk)) z hz.2⟩)
      (fun z hz => ?_)
    have hzC : z ∈ Subgroup.centralizer (fsuV T I : Set G) :=
      Subgroup.centralizer_le (le_conjClosure (fsuV T I) G₁) hz.2
    have hzV : z ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.centralizer_le_normalizer _ hzC
    exact mem_normalizer_lOf (SecA.normalizer_fsuV_le h331 h hzV) (hKG₁ hz.1)
  have hUZ : U ≤ Subgroup.normalizer (Zc : Set G) := fun u hu =>
    hZnorm ((h5one.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) hu)
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := hKG₁.trans hG₁U
  have hKZ : K ≤ Subgroup.normalizer (Zc : Set G) := hKG₁.trans hZnorm
  have hV₁Z : V₁ ≤ Zc := hZeq ▸ le_sup_left
  have : (Zc.subgroupOf U).Normal := normal_subgroupOf_of_le inf_le_left hUZ
  refine hF2 G K n hlist hcase1 hKperf (↥U ⧸ Zc.subgroupOf U) ?_ ?_ ?_ (quotAct hKU hKZ) ?_
  · intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
          Subgroup.coe_mul]
        have h1 := hV₁Z (hUcomm _ (U.inv_mem b.2) _ (U.inv_mem a.2))
        convert h1 using 1
        group
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hV₁Z (hUsq a a.2)
  · exact hrel.le
  · intro k hk
    have hk' := (quotAct_eq_one_iff hUZ hKU hKZ k).mp hk
    refine hCK ⟨K.pow_mem k.2 2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hz := hk' u hu
    set c := (k : G) * u * (k : G)⁻¹ * u⁻¹ with hc
    have hkz : (k : G) * c = c * k := (Subgroup.mem_centralizer_iff.mp (hKC k.2) _ hz).symm
    have hz2 : c ^ 2 = 1 := hSs _ (hZS hz)
    have e1 : (k : G) * u * (k : G)⁻¹ = c * u := by rw [hc]; group
    have hkc : (k : G) * c * (k : G)⁻¹ = c := by rw [hkz, mul_inv_cancel_right]
    have e2 : (k : G) ^ 2 * u * ((k : G) ^ 2)⁻¹ = u := by
      calc (k : G) ^ 2 * u * ((k : G) ^ 2)⁻¹ =
            (k : G) * ((k : G) * u * (k : G)⁻¹) * (k : G)⁻¹ := by rw [pow_two, mul_inv_rev]; group
        _ = (k : G) * (c * u) * (k : G)⁻¹ := by rw [e1]
        _ = ((k : G) * c * (k : G)⁻¹) * ((k : G) * u * (k : G)⁻¹) := by group
        _ = c * (c * u) := by rw [hkc, e1]
        _ = c ^ 2 * u := by rw [pow_two]; exact (mul_assoc c c u).symm
        _ = u := by rw [hz2, one_mul]
    calc u * (k : G) ^ 2 = (k : G) ^ 2 * u * ((k : G) ^ 2)⁻¹ * (k : G) ^ 2 := by rw [e2]
      _ = (k : G) ^ 2 * u := by group

end CFSG.Quasithin.Vol2.Ch11.SecD
