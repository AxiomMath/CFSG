module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_9_statement
    {G : Type u} [Group G] [Finite G]
    (W W1 W2 S T SF TF U W2S : Subgroup G) : Prop :=
  theorem_8_8_source_case_b_data W W1 W2 S T SF TF →
    typePDefinitionData S SF U W1 W2S →
      W2 = W2S

/-- Peterfalvi Definition and Notation `(8.10)`. -/


private theorem section8ComplementIn_isComplement'_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    (L.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hKM, hLM, hsup, hdisj⟩
  have hsup_local : L.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    calc
      L.subgroupOf M ⊔ K.subgroupOf M = (L ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := M) hLM hKM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf M) (K.subgroupOf M)).symm

private theorem section8_subgroup_le_of_subgroupOf_quotient_map_eq_bot
    {G : Type u} [Group G] {N L C : Subgroup G} [hN : (N.subgroupOf L).Normal]
    (hCL : C ≤ L)
    (hmap : (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) = ⊥) :
    C ≤ N := by
  intro x hxC
  have hxsub : (⟨x, hCL hxC⟩ : L) ∈ C.subgroupOf L := by
    simpa [Subgroup.mem_subgroupOf] using hxC
  have hxmap :
      QuotientGroup.mk' (N.subgroupOf L) (⟨x, hCL hxC⟩ : L) ∈
        (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (N.subgroupOf L)) hxsub
  have hxbot :
      QuotientGroup.mk' (N.subgroupOf L) (⟨x, hCL hxC⟩ : L) = 1 := by
    simpa [hmap] using hxmap
  have hxker : (⟨x, hCL hxC⟩ : L) ∈ (QuotientGroup.mk' (N.subgroupOf L)).ker := by
    simpa [MonoidHom.mem_ker] using hxbot
  have hxNsub : (⟨x, hCL hxC⟩ : L) ∈ N.subgroupOf L := by
    simpa [QuotientGroup.ker_mk'] using hxker
  simpa [Subgroup.mem_subgroupOf] using hxNsub

/-- In a cyclic internal direct product, the two factors have coprime orders. -/
private theorem section8_natCard_coprime_of_section12InternalDirectProduct_cyclic
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcyc : IsCyclic W) :
    Nat.Coprime (Nat.card W1) (Nat.card W2) := by
  classical
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  let J : Subgroup G := W1 ⊔ W2
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) :=
    hcent.trans (centralizer_le_normalizer W2)
  let W1J : Subgroup J := W1.subgroupOf J
  let W2J : Subgroup J := W2.subgroupOf J
  haveI : W2J.Normal := by
    simpa [J, W2J] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  let f : W1 × W2 →* W :=
    { toFun := fun p =>
        ⟨(p.1 : G) * (p.2 : G), W.mul_mem (hW1le p.1.2) (hW2le p.2.2)⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro p q
        ext
        have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          (Subgroup.mem_centralizer_iff.mp (hcent q.1.2) (p.2 : G) p.2.2).symm
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc
          ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
              (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by
                simp [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hcomm]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by
                simp [mul_assoc] }
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    have hmul : (h₁ : G) * (k₁ : G) = (h₂ : G) * (k₂ : G) :=
      Subtype.ext_iff.mp heq
    have hleft_eq_right : (h₂ : G)⁻¹ * (h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by
      calc
        (h₂ : G)⁻¹ * (h₁ : G) =
            (h₂ : G)⁻¹ * ((h₁ : G) * (k₁ : G)) * (k₁ : G)⁻¹ := by
              simp [mul_assoc]
        _ = (h₂ : G)⁻¹ * ((h₂ : G) * (k₂ : G)) * (k₁ : G)⁻¹ := by
              rw [hmul]
        _ = (k₂ : G) * (k₁ : G)⁻¹ := by
              simp
    have hmemW1 : (h₂ : G)⁻¹ * (h₁ : G) ∈ W1 :=
      W1.mul_mem (W1.inv_mem h₂.2) h₁.2
    have hmemW2 : (h₂ : G)⁻¹ * (h₁ : G) ∈ W2 := by
      rw [hleft_eq_right]
      exact W2.mul_mem k₂.2 (W2.inv_mem k₁.2)
    have hh_eq_one : (h₂ : G)⁻¹ * (h₁ : G) = 1 :=
      Subgroup.disjoint_def.mp hdisj hmemW1 hmemW2
    have hh : h₁ = h₂ := by
      apply Subtype.ext
      calc
        (h₁ : G) = (h₂ : G) * ((h₂ : G)⁻¹ * (h₁ : G)) := by simp
        _ = (h₂ : G) := by simp [hh_eq_one]
    have hk : k₁ = k₂ := by
      apply Subtype.ext
      have hmul' := congrArg (fun z : G => (h₂ : G)⁻¹ * z) hmul
      simpa [hh, mul_assoc] using hmul'
    exact Prod.ext hh hk
  have hf_surj : Function.Surjective f := by
    intro w
    let j : J := ⟨(w : G), by simp [J, ← hW, w.2]⟩
    have htop : W1J ⊔ W2J = ⊤ := by
      simpa [J, W1J, W2J] using
        (Subgroup.subgroupOf_sup (A := W1) (A' := W2) (B := J)
          le_sup_left le_sup_right).symm
    have hjmem : j ∈ W1J ⊔ W2J := by
      rw [htop]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right.mp hjmem) with ⟨x, hx, y, hy, hxy⟩
    refine ⟨(⟨(x : G), by simpa [W1J, Subgroup.mem_subgroupOf] using hx⟩,
      ⟨(y : G), by simpa [W2J, Subgroup.mem_subgroupOf] using hy⟩), ?_⟩
    ext
    change (x : G) * (y : G) = (w : G)
    simpa [j] using congrArg Subtype.val hxy
  let e : W1 × W2 ≃* W := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hprodcyc : IsCyclic (W1 × W2) := e.isCyclic.mpr hcyc
  letI : IsCyclic (W1 × W2) := hprodcyc
  simpa [Nat.card_eq_fintype_card] using coprime_card_of_isCyclic_prod W1 W2

private theorem caseB_W2_le_ambientDerived_S
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcyc : IsCyclic W)
    (hW_le_S : W ≤ S)
    (hcompS : section12ComplementIn S (ambientDerivedSubgroup S) W1) :
    W2 ≤ ambientDerivedSubgroup S := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup S
  have hW2_le_S : W2 ≤ S := hprod.2.1.trans hW_le_S
  have hDnorm : (D.subgroupOf S).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := S)).2
  letI : (D.subgroupOf S).Normal := hDnorm
  let q : S →* S ⧸ D.subgroupOf S := QuotientGroup.mk' (D.subgroupOf S)
  let W2sub : Subgroup S := W2.subgroupOf S
  have hcompLocal : (W1.subgroupOf S).IsComplement' (D.subgroupOf S) :=
    section8ComplementIn_isComplement'_subgroupOf
      (M := S) (K := D) (L := W1) (by simpa [D] using hcompS)
  have hquot_card : Nat.card (S ⧸ D.subgroupOf S) = Nat.card W1 := by
    calc
      Nat.card (S ⧸ D.subgroupOf S) = (D.subgroupOf S).index := by
        simpa using (Subgroup.index_eq_card (D.subgroupOf S)).symm
      _ = Nat.card (W1.subgroupOf S) := hcompLocal.index_eq_card
      _ = Nat.card W1 := natCard_subgroupOf_eq W1 S hcompS.2.1
  have hmap_dvd_quot : Nat.card (W2sub.map q) ∣ Nat.card W1 := by
    have h : Nat.card (W2sub.map q) ∣ Nat.card (S ⧸ D.subgroupOf S) :=
      Subgroup.card_subgroup_dvd_card (W2sub.map q)
    simpa [hquot_card] using h
  have hmap_dvd_W2 : Nat.card (W2sub.map q) ∣ Nat.card W2 := by
    have h : Nat.card (W2sub.map q) ∣ Nat.card W2sub :=
      Subgroup.card_map_dvd W2sub q
    simpa [W2sub, natCard_subgroupOf_eq W2 S hW2_le_S] using h
  have hcop : Nat.Coprime (Nat.card W1) (Nat.card W2) :=
    section8_natCard_coprime_of_section12InternalDirectProduct_cyclic hprod hcyc
  have hmap_card_one : Nat.card (W2sub.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hmap_dvd_quot hmap_dvd_W2
  have hmap_bot : W2sub.map q = ⊥ :=
    (Subgroup.card_eq_one (H := W2sub.map q)).1 hmap_card_one
  exact section8_subgroup_le_of_subgroupOf_quotient_map_eq_bot
    (N := D) (L := S) (C := W2) hW2_le_S hmap_bot

private theorem typeP_W2_le_ambientDerived_89
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ ambientDerivedSubgroup M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  exact hW2le.trans inf_le_right |>.trans
    (section12_ambientDerivedSubgroup_mono (G := G)
      (section12_ambientDerivedSubgroup_le (G := G) (E := M)))

private theorem typeP_W2_le_centralizer_W1_89
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    W2 ≤ Subgroup.centralizer (W1 : Set G) := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      hcentW1, _hnormX⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
      simpa [hcentW1 x hx hx1] using hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm

private theorem section8_mem_normalizer_singleton_of_mem_centralizer_singleton
    {G : Type u} [Group G] {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    c ∈ Subgroup.normalizer ({a} : Set G) := by
  have hcomm : c * a = a * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hfix : c * a * c⁻¹ = a := by
    calc
      c * a * c⁻¹ = a * c * c⁻¹ := by rw [hcomm]
      _ = a := by simp [mul_assoc]
  change ∀ y : G, y ∈ ({a} : Set G) ↔ c * y * c⁻¹ ∈ ({a} : Set G)
  intro y
  constructor
  · intro hy
    have hy_eq : y = a := by simpa using hy
    simp [hy_eq, hfix]
  · intro hy
    have hy_eq : c * y * c⁻¹ = a := by simpa using hy
    have hfix_inv : c⁻¹ * a * c = a := by
      have h := congrArg (fun z : G => c⁻¹ * z * c) hfix
      simpa [mul_assoc] using h.symm
    have hy_a : y = a := by
      calc
        y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = c⁻¹ * a * c := by rw [hy_eq]
        _ = a := hfix_inv
    simp [hy_a]

private theorem caseB_W2_le_typeP_W2
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S SF U W2S : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hW1ne : W1 ≠ ⊥)
    (hW2_le_D : W2 ≤ ambientDerivedSubgroup S)
    (hP : typePDefinitionData S SF U W1 W2S) :
    W2 ≤ W2S := by
  rcases hprod with ⟨_hW1le, _hW2le, _hW, _hdisj, hcent⟩
  rcases hP with
    ⟨_hSF, _hW1cyc, _hW1neP, _hW1hall, _hcompSW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hSFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2Sle, _hW2Scyc,
      _hW2Sne, hcentW1, _hnormX⟩
  obtain ⟨a, haW1, ha1⟩ : ∃ a : G, a ∈ W1 ∧ a ≠ 1 := by
    by_contra hnone
    apply hW1ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  intro y hyW2
  have hyCentSingleton : y ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hcent haW1) y hyW2
  have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup S) a :=
    ⟨hW2_le_D hyW2, hyCentSingleton⟩
  simpa [hcentW1 a haW1 ha1] using hyCent

private theorem caseB_W2S_le_W2
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S SF U W2S : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcyc : IsCyclic W)
    (hW1ne : W1 ≠ ⊥) (hW2ne : W2 ≠ ⊥)
    (hnormW : ∀ W0 : Set G, W0.Nonempty →
      W0 ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) →
        Subgroup.normalizer W0 = W)
    (hcompS : section12ComplementIn S (ambientDerivedSubgroup S) W1)
    (hW2_le_D : W2 ≤ ambientDerivedSubgroup S)
    (hW2_le_W2S : W2 ≤ W2S)
    (hP : typePDefinitionData S SF U W1 W2S) :
    W2S ≤ W2 := by
  classical
  rcases hprod with ⟨hW1leW, hW2leW, hW, hdisj, _hcent⟩
  have hW2S_le_D : W2S ≤ ambientDerivedSubgroup S :=
    typeP_W2_le_ambientDerived_89 hP
  have hW2S_cent_W1 : W2S ≤ Subgroup.centralizer (W1 : Set G) :=
    typeP_W2_le_centralizer_W1_89 hP
  rcases hP with
    ⟨_hSF, _hW1cyc, _hW1neP, _hW1hall, _hcompSW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, _hSFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2Sle, hW2Scyc,
      _hW2Sne, _hcentW1, _hnormX⟩
  obtain ⟨a, haW1, ha1⟩ : ∃ a : G, a ∈ W1 ∧ a ≠ 1 := by
    by_contra hnone
    apply hW1ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  obtain ⟨b, hbW2, hb1⟩ : ∃ b : G, b ∈ W2 ∧ b ≠ 1 := by
    by_contra hnone
    apply hW2ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  let v : G := a * b
  have hvV : v ∈ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
    constructor
    · rw [hW]
      exact Subgroup.mul_mem_sup haW1 hbW2
    · intro hvbad
      rcases hvbad with hvW1 | hvW2
      · have hbW1 : b ∈ W1 := by
          have h : a⁻¹ * v ∈ W1 := W1.mul_mem (W1.inv_mem haW1) hvW1
          simpa [v, mul_assoc] using h
        have hbBot : b ∈ (⊥ : Subgroup G) := hdisj.le_bot ⟨hbW1, hbW2⟩
        exact hb1 (by simpa using hbBot)
      · have haW2 : a ∈ W2 := by
          have h : v * b⁻¹ ∈ W2 := W2.mul_mem hvW2 (W2.inv_mem hbW2)
          simpa [v, mul_assoc] using h
        have haBot : a ∈ (⊥ : Subgroup G) := hdisj.le_bot ⟨haW1, haW2⟩
        exact ha1 (by simpa using haBot)
  have hnormSingleton : Subgroup.normalizer ({v} : Set G) = W :=
    hnormW ({v} : Set G) ⟨v, rfl⟩ (by
      intro y hy
      have hy_eq : y = v := by simpa using hy
      simpa [hy_eq] using hvV)
  intro y hyW2S
  have hyCentV : y ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hya : y * a = a * y :=
      (Subgroup.mem_centralizer_iff.mp (hW2S_cent_W1 hyW2S) a haW1).symm
    have hyb : y * b = b * y := by
      letI : IsCyclic W2S := hW2Scyc
      exact setLike_mul_comm
        (s := W2S) hyW2S (hW2_le_W2S hbW2)
    calc
      y * v = y * (a * b) := rfl
      _ = (y * a) * b := by simp [mul_assoc]
      _ = (a * y) * b := by rw [hya]
      _ = a * (y * b) := by simp [mul_assoc]
      _ = a * (b * y) := by rw [hyb]
      _ = (a * b) * y := by simp [mul_assoc]
      _ = v * y := rfl
  have hyNorm : y ∈ Subgroup.normalizer ({v} : Set G) :=
    section8_mem_normalizer_singleton_of_mem_centralizer_singleton hyCentV
  have hyW : y ∈ W := by
    simpa [hnormSingleton] using hyNorm
  let W1W : Subgroup W := W1.subgroupOf W
  let W2W : Subgroup W := W2.subgroupOf W
  let yW : W := ⟨y, hyW⟩
  letI : IsCyclic W := hcyc
  letI : CommGroup W := IsCyclic.commGroup
  have hsupTop : W1W ⊔ W2W = ⊤ := by
    calc
      W1W ⊔ W2W = (W1 ⊔ W2).subgroupOf W := by
        symm
        exact Subgroup.subgroupOf_sup (A := W1) (A' := W2) (B := W) hW1leW hW2leW
      _ = W.subgroupOf W := by rw [← hW]
      _ = ⊤ := by simp
  have hyTop : yW ∈ W1W ⊔ W2W := by
    rw [hsupTop]
    trivial
  rcases Subgroup.mem_sup.mp hyTop with ⟨aW, haW1W, bW, hbW2W, hab⟩
  let a0 : G := aW
  let b0 : G := bW
  have ha0W1 : a0 ∈ W1 := by
    simpa [a0, W1W, Subgroup.mem_subgroupOf] using haW1W
  have hb0W2 : b0 ∈ W2 := by
    simpa [b0, W2W, Subgroup.mem_subgroupOf] using hbW2W
  have hy_eq : y = a0 * b0 := by
    have hval := congrArg (fun z : W => (z : G)) hab
    simpa [a0, b0, yW] using hval.symm
  have hb0D : b0 ∈ ambientDerivedSubgroup S := hW2_le_D hb0W2
  have ha0D : a0 ∈ ambientDerivedSubgroup S := by
    have h : y * b0⁻¹ ∈ ambientDerivedSubgroup S :=
      (ambientDerivedSubgroup S).mul_mem (hW2S_le_D hyW2S)
        ((ambientDerivedSubgroup S).inv_mem hb0D)
    have ha_eq : a0 = y * b0⁻¹ := by
      calc
        a0 = (a0 * b0) * b0⁻¹ := by simp [mul_assoc]
        _ = y * b0⁻¹ := by rw [← hy_eq]
    simpa [ha_eq] using h
  have ha0Bot : a0 ∈ (⊥ : Subgroup G) :=
    hcompS.2.2.2.le_bot ⟨ha0D, ha0W1⟩
  have ha0_one : a0 = 1 := by simpa using ha0Bot
  have hy_eq_b0 : y = b0 := by
    rw [hy_eq, ha0_one]
    simp
  simpa [hy_eq_b0] using hb0W2

public theorem theorem_8_9
    {G : Type u} [Group G] [Finite G]
    (W W1 W2 S T SF TF U W2S : Subgroup G) :
    theorem_8_9_statement W W1 W2 S T SF TF U W2S := by
  dsimp [theorem_8_9_statement]
  intro hcase hP
  rcases hcase with
    ⟨hprod, hWcyc, hW1ne, hW2ne, hnormW, _hSmax, _hTmax, _hSF, _hTF,
      hSeq, _hTeq, hSdisj, _hTdisj, hST, _hTypeII, _hSType, _hTType, _hcover⟩
  have hW_le_S : W ≤ S := by
    intro x hxW
    have hxST : x ∈ S ⊓ T := by
      simpa [hST] using hxW
    exact hxST.1
  have hcompS : section12ComplementIn S (ambientDerivedSubgroup S) W1 :=
    ⟨section12_ambientDerivedSubgroup_le,
      hprod.1.trans hW_le_S, hSeq, hSdisj⟩
  have hW2_le_D : W2 ≤ ambientDerivedSubgroup S :=
    caseB_W2_le_ambientDerived_S
      (W := W) (W1 := W1) (W2 := W2) (S := S)
      hprod hWcyc hW_le_S hcompS
  have hW2_le_W2S : W2 ≤ W2S :=
    caseB_W2_le_typeP_W2
      (W := W) (W1 := W1) (W2 := W2) (S := S) (SF := SF) (U := U)
      (W2S := W2S) hprod hW1ne hW2_le_D hP
  have hW2S_le_W2 : W2S ≤ W2 :=
    caseB_W2S_le_W2
      (W := W) (W1 := W1) (W2 := W2) (S := S) (SF := SF) (U := U)
      (W2S := W2S) hprod hWcyc hW1ne hW2ne hnormW hcompS hW2_le_D
      hW2_le_W2S hP
  exact le_antisymm hW2_le_W2S hW2S_le_W2

end CFSG.Section8
