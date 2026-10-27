module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Triple
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Apply

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L15420

variable {G : Type*} [Group G]

theorem not_le_pCoreOf {L : Subgroup G} (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ L ≤ pCoreOf 2 L := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  have key : ∀ x : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L), x = 1 := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [mk_eq_one_iff.mpr (h x.2)]
    rfl
  rw [key a, key b]

theorem not_mem_of_orderOf_eq_three {P : Subgroup G} (hP : IsPGroup 2 P) {y : G}
    (hy : orderOf y = 3) : y ∉ P := by
  intro hyP
  obtain ⟨m, hm⟩ := hP ⟨y, hyP⟩
  have hym : y ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hdvd : 3 ∣ 2 ^ m := hy ▸ orderOf_dvd_of_pow_eq_one hym
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem quasithinIsSylowTwo_map {L S : Subgroup G} (hS : IsSylowTwoOf S L) :
    quasithinIsSylowTwo ((S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
  ⟨(hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map _, fun h =>
    hS.2.2 (h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))⟩

theorem quotConj_mul_self {L : Subgroup G} {z : G} (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hz2 : z * z = 1) : quotConj L z hz * quotConj L z hz = 1 := by
  rw [← quotConj_mul hz hz, quotConj_congr hz2 _ (Subgroup.one_mem _), quotConj_one]

theorem quotConj_ne_one {L : Subgroup G} (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {z : G}
    (hz : z ∈ Subgroup.normalizer (L : Set G)) (hz2 : z * z = 1)
    (hLz : ⁅L, Subgroup.zpowers z⁆ = L) : quotConj L z hz ≠ 1 := by
  intro h1
  apply not_le_pCoreOf hq
  refine hLz.ge.trans ?_
  rw [Subgroup.commutator_le]
  intro l hl w hw
  rcases eq_one_or_eq_of_mem_zpowers hz2 hw with rfl | rfl
  · simp
  · have h := (quotConj_eq_one_iff hz).mp h1 l⁻¹ (L.inv_mem hl)
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl
    have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp h
    rw [commutatorElement_def]
    convert h2 using 1
    group

end L15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Comp15420

variable {s : Setting15419 G T} {I₀ L : Subgroup G} {y : G}

omit [Finite G] in
theorem center_eq_bot (facts : Facts15420) (hC : Comp15420 s I₀ L y) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  rcases hC.type with (⟨n, -, h⟩ | ⟨q, -, -, h⟩) | ⟨-, h | h | h | h | h | h⟩
  · exact facts.centerPSL _ _ _ _ h
  · exact facts.centerPSL _ _ _ _ h
  · exact facts.centerPSL _ _ _ _ h
  · exact facts.centerSL33M11 _ (Or.inl h)
  · exact facts.centerSL33M11 _ (Or.inr h)
  · exact facts.centerPSL _ _ _ _ h
  · exact facts.centerPSL _ _ _ _ h
  · exact facts.centerHe _ h

theorem X_le_normalizer (hC : Comp15420 s I₀ L y) :
    s.X ≤ Subgroup.normalizer (L : Set G) := by
  refine hC.le.trans (conjClosure_le fun g hg l hl => ?_)
  have hL' : L.map (MulAut.conj g).toMonoidHom ∈ cComp I₀ := by
    have h1 := cComp_map_mulEquiv (MulAut.conj g) hC.mem
    rwa [map_conj_eq_self_of_mem hg.2] at h1
  exact le_normalizer_of_mem_cComp hC.mem hL' ⟨l, hl, rfl⟩

theorem not_mem_pCoreOf (hC : Comp15420 s I₀ L y) : y ∉ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact L15420.not_mem_of_orderOf_eq_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    hC.y_order

end Comp15420

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem exists_lemma115Hyp (hyp : MultipleCentralizerHypothesis G T) (h17 : Stmt15417 G T)
    (c : Config15420 s I₀) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    ∃ Mz : Subgroup G, Lemma115Hyp I₀ (T ⊓ I₀) Mz z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := pCoreOf 2 I₀ with hBdef
  set H := Subgroup.normalizer (B : Set G) with hHdef
  have hBT : B ≤ T ⊓ I₀ := L15420.pCoreOf_le_of_isSylowTwoOf c.sylow
  have hI₀H : I₀ ≤ H := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I₀
  have hBH : B ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I₀)
  have hHinH : InH s.I H :=
    ⟨c.inH.1.trans hI₀H, fun h => c.inH.2 (le_bot_iff.mp (h ▸ hBH))⟩
  have hsylH : IsSylowTwoOf (T ⊓ I₀) H := c.sylow_of_le H hHinH (inf_le_right.trans hI₀H)
  have hTH : T ⊓ H = T ⊓ I₀ := inf_eq_of_isSylowTwoOf_of_le hsylH hyp.sylow.1 inf_le_left
  have hsyl' : IsSylowTwoOf (T ⊓ H) H := hTH ▸ hsylH
  obtain ⟨h1, -⟩ := h17 B H I₀ c.inH.2 (hBT.trans inf_le_left)
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)) le_rfl hsyl'
    (hTH ▸ inf_le_right) hI₀H
  obtain ⟨Mz, hMz⟩ := exists_inM_centralizer hz hz1
  refine ⟨Mz, ?_⟩
  have := h1 z hz hz1 Mz hMz
  rwa [hTH] at this

theorem false_of_isComponentIn (facts : Facts15420) (hyp : MultipleCentralizerHypothesis G T)
    (hnot : ¬ IsLThreeTwoOrASix G) (h12 : Stmt15412 G T) (h14 : Stmt15414 G T)
    (h17 : Stmt15417 G T) (c : Config15420 s I₀) {L : Subgroup G} {y : G}
    (hC : Comp15420 s I₀ L y) (hcomp : IsComponentIn L I₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZc := hC.center_eq_bot facts
  have hq := hC.quasisimple
  have hyX : y ∈ s.X := hC.y_mem.1
  have hyL : y ∈ L := hC.y_mem.2
  have hZT : ∀ z ∈ Z, z ∈ T ∧ z ∈ Subgroup.centralizer (T : Set G) := fun z hz =>
    L15420.omegaOneCenter_le_center T hz
  have hZ2 : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    rw [← sq]
    exact sq_eq_one_of_mem_omegaOneCenter T hz
  have hact : ∀ z ∈ Z, z ≠ 1 → z ∈ Subgroup.normalizer (L : Set G) ∧
      ⁅L, Subgroup.zpowers z⁆ = L := by
    intro z hz hz1
    obtain ⟨Mz, hMz⟩ := c.exists_lemma115Hyp hyp h17 hz hz1
    obtain ⟨hzN, hLz, -, -⟩ := hMz.component_action hcomp
    exact ⟨hzN, hLz⟩
  have hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer (L : Set G) := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    · exact (hact z hz hz1).1
  have hρ : ∀ z (hz : z ∈ Z), z ≠ 1 → L15420.quotConj L z (hZN z hz) ≠ 1 := fun z hz hz1 =>
    L15420.quotConj_ne_one hq (hZN z hz) (hZ2 z hz) (hact z hz hz1).2
  set TL := (T ⊓ I₀) ⊓ L with hTLdef
  have hTL : IsSylowTwoOf TL L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hC.mem) c.sylow
  set Sb := (TL.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hSbdef
  have hSb : quasithinIsSylowTwo Sb := L15420.quasithinIsSylowTwo_map hTL
  have hfix : ∀ z (hz : z ∈ Z), ∀ x ∈ Sb, L15420.quotConj L z (hZN z hz) x = x := by
    intro z hz x hx
    obtain ⟨l, hl, rfl⟩ := hx
    have hlT : (l : G) ∈ T := hl.1.1
    exact L15420.quotConj_fix (hZN z hz)
      (Subgroup.mem_centralizer_iff.mp (hZT z hz).2 _ hlT).symm
  obtain ⟨-, hZ4'⟩ := h14 hnot
  have hZ4 : Nat.card Z = 4 := hZ4'
  obtain ⟨z₁, hz₁, hz₁1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left (by
    intro h
    rw [h, Subgroup.card_bot] at hZ4
    omega)
  obtain ⟨z₂, hz₂, hz₂n⟩ : ∃ z₂ ∈ Z, z₂ ∉ Subgroup.zpowers z₁ := by
    by_contra h
    push Not at h
    have hle : Z ≤ Subgroup.zpowers z₁ := h
    have h1 := Subgroup.card_le_of_le hle
    have h2 : orderOf z₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hZ2 z₁ hz₁) hz₁1
    rw [Nat.card_zpowers, h2, hZ4] at h1
    omega
  have hz₂1 : z₂ ≠ 1 := fun h => hz₂n (h ▸ Subgroup.one_mem _)
  have hz₁₂ : z₁ * z₂ ≠ 1 := by
    intro h
    apply hz₂n
    have e : z₂ = z₁ := by
      calc z₂ = (z₁ * z₁) * z₂ := by rw [hZ2 z₁ hz₁, one_mul]
        _ = z₁ * (z₁ * z₂) := by group
        _ = z₁ := by rw [h, mul_one]
    rw [e]
    exact Subgroup.mem_zpowers z₁
  have hcomm₁₂ : z₁ * z₂ = z₂ * z₁ :=
    Subgroup.mem_centralizer_iff.mp (hZT z₂ hz₂).2 _ (hZT z₁ hz₁).1
  set α := L15420.quotConj L z₁ (hZN z₁ hz₁) with hαdef
  set β := L15420.quotConj L z₂ (hZN z₂ hz₂) with hβdef
  have hα1 : α ≠ 1 := hρ z₁ hz₁ hz₁1
  have hβ1 : β ≠ 1 := hρ z₂ hz₂ hz₂1
  have hαβ' : α * β = L15420.quotConj L (z₁ * z₂) (hZN _ (Z.mul_mem hz₁ hz₂)) :=
    (L15420.quotConj_mul _ _).symm
  have hαβ : α ≠ β := by
    intro h
    apply hρ _ (Z.mul_mem hz₁ hz₂) hz₁₂
    rw [← hαβ', h]
    exact L15420.quotConj_mul_self _ (hZ2 z₂ hz₂)
  have hcomm : α * β = β * α := by
    rw [hαβ', ← L15420.quotConj_mul]
    exact L15420.quotConj_congr hcomm₁₂ _ _
  have hα2 : α * α = 1 := L15420.quotConj_mul_self _ (hZ2 z₁ hz₁)
  have hβ2 : β * β = 1 := L15420.quotConj_mul_self _ (hZ2 z₂ hz₂)
  rcases hC.type with (⟨n, -, hmodel⟩ | ⟨q, hqp, hq2, hmodel⟩) | ⟨-, htype⟩
  ·
    obtain ⟨zX, hzX, hzX1, hzXC, -⟩ := exists_zX hnot h12 h14 s
    set yb : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨y, hyL⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) with hybdef
    have hyb3 : orderOf yb = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [hybdef, ← QuotientGroup.mk_pow]
        have : (⟨y, hyL⟩ : L) ^ 3 = 1 := Subtype.ext (by
          simp [← hC.y_order, pow_orderOf_eq_one])
        rw [this, QuotientGroup.mk_one]
      · intro h
        exact hC.not_mem_pCoreOf (L15420.mk_eq_one_iff.mp h)
    have hfy : L15420.quotConj L zX (hZN zX hzX) yb = yb :=
      L15420.quotConj_fix (hZN zX hzX) (Subgroup.mem_centralizer_iff.mp hzXC y hyX).symm
    exact hρ zX hzX hzX1 (facts.autPSL2Even _ n hmodel Sb hSb yb hyb3 _ (hfix zX hzX) hfy)
  ·
    obtain ⟨g, hgTI, hginv⟩ := c.exists_inverting hyp h12
    have hNL : pCoreOf 2 s.X ≤ Subgroup.normalizer (L : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 s.X).trans hC.X_le_normalizer
    have hgN : g ∈ Subgroup.normalizer (L : Set G) := by
      refine L15420.mem_normalizer_of_conj_mem hC.mem hq hZc hyL hC.y_order hgTI.2
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.X) hNL (ε := -1) (Or.inr rfl) ?_
      simpa using hginv y hyX
    set γ := L15420.quotConj L g hgN with hγdef
    have hgz : ∀ z ∈ Z, g * z = z * g := fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZT z hz).2 _ hgTI.1)
    have hγc : ∀ z (hz : z ∈ Z), γ * L15420.quotConj L z (hZN z hz) =
        L15420.quotConj L z (hZN z hz) * γ := by
      intro z hz
      rw [← L15420.quotConj_mul, ← L15420.quotConj_mul]
      exact L15420.quotConj_congr (hgz z hz) _ _
    have hcases := facts.autPSL2Odd _ q hqp hq2 hmodel Sb hSb α β γ (hfix z₁ hz₁) (hfix z₂ hz₂)
      hα1 hβ1 hαβ hcomm hα2 hβ2 (hγc z₁ hz₁) (hγc z₂ hz₂)
    obtain ⟨z, hz, hγz⟩ : ∃ z, ∃ hz : z ∈ Z, γ = L15420.quotConj L z (hZN z hz) := by
      rcases hcases with h | h | h | h
      · refine ⟨1, Z.one_mem, ?_⟩
        rw [h]
        exact L15420.quotConj_one.symm
      · exact ⟨z₁, hz₁, h⟩
      · exact ⟨z₂, hz₂, h⟩
      · exact ⟨z₁ * z₂, Z.mul_mem hz₁ hz₂, h.trans hαβ'⟩
    have hw : L15420.quotConj L (g * z) (Subgroup.mul_mem _ hgN (hZN z hz)) = 1 := by
      rw [L15420.quotConj_mul hgN (hZN z hz), ← hγdef, hγz,
        L15420.quotConj_mul_self _ (hZ2 z hz)]
    have hq₀ := (L15420.quotConj_eq_one_iff _).mp hw y hyL
    have hzR : z ∈ pCoreOf 2 (s.X ⊔ T ⊓ I₀) := c.omegaOneCenter_le_R hyp hz
    have hn₁ : z * y * z⁻¹ * y⁻¹ ∈ pCoreOf 2 s.X := by
      have h := c.commutator_X_R_le hyp h12 (Subgroup.commutator_mem_commutator hyX hzR)
      have h' := (pCoreOf 2 s.X).inv_mem h
      simpa [commutatorElement_def, mul_assoc] using h'
    have hn₂ := hginv y hyX
    have hgQ : g * (z * y * z⁻¹ * y⁻¹) * g⁻¹ ∈ pCoreOf 2 s.X := by
      have hgX : g ∈ Subgroup.normalizer (s.X : Set G) :=
        s.inM₁.2.trans (M₁_le_normalizer_X h12 s) hgTI.1
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.X hgX) _).mp hn₁
    set m := g * (z * y * z⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y) with hmdef
    set qq := g * z * y * (g * z)⁻¹ * y⁻¹ with hqqdef
    have hmQ : m ∈ pCoreOf 2 s.X := (pCoreOf 2 s.X).mul_mem hgQ hn₂
    have hy3 : y ^ 3 = 1 := by rw [← hC.y_order, pow_orderOf_eq_one]
    have e : m⁻¹ * qq = y := by
      have e1 : m⁻¹ * qq = y⁻¹ * y⁻¹ := by
        rw [hmdef, hqqdef]
        group
      rw [e1]
      calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * y ^ 3 := by rw [hy3, mul_one]
        _ = y := by group
    have h2grp : IsPGroup 2 ↥(pCoreOf 2 s.X ⊔ pCoreOf 2 L) :=
      IsPGroup.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.X)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
        (hNL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    refine L15420.not_mem_of_orderOf_eq_three h2grp hC.y_order ?_
    rw [← e]
    exact Subgroup.mul_mem_sup ((pCoreOf 2 s.X).inv_mem hmQ) hq₀
  ·
    have hsmall : ∀ S : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), quasithinIsSylowTwo S →
        ∀ α β : MulAut (↥L ⧸ CFSG.pCore 2 ↥L), (∀ s ∈ S, α s = s) → (∀ s ∈ S, β s = s) →
          α * β = β * α → α * α = 1 → β * β = 1 → α = 1 ∨ β = 1 ∨ α = β := by
      rcases htype with h | h | h | h | h | h
      · exact facts.autSmallCentralizer _ (Or.inl h)
      · exact facts.autSmallCentralizer _ (Or.inr (Or.inl h))
      · exact facts.autSmallCentralizer _ (Or.inr (Or.inr (Or.inl h)))
      · exact facts.autSmallCentralizer _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact facts.autSmallCentralizer _ (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact facts.autHe _ h
    rcases hsmall Sb hSb α β (hfix z₁ hz₁) (hfix z₂ hz₂) hcomm hα2 hβ2 with h | h | h
    · exact hα1 h
    · exact hβ1 h
    · exact hαβ h

end Config15420

end CFSG.Quasithin.EmptyFaithfulMultiple
