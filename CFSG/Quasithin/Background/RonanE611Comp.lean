module

public import CFSG.Quasithin.Background.RonanE611Frat
public import CFSG.Quasithin.Background.RonanE611Exp
public import CFSG.Quasithin.Background.RonanE611Sp4
public import CFSG.Quasithin.Background.RonanE611NH
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NoLocalQuasisimpleComponent
public import CFSG.Quasithin.Background.RonanE611Clause
public import CFSG.Quasithin.Background.RonanE611X

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.E68Proof

section Setting

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

structure Setting (M V U L : Subgroup G) : Prop where
  comp : IsComponentIn L (Subgroup.centralizer (U : Set G))
  notM : ¬ L ≤ M
  cv : V ⊓ Subgroup.centralizer (L : Set G) = U
  vn : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)
  ln : (L.subgroupOf (Subgroup.centralizer (U : Set G))).Normal
  uniq : ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer (U : Set G)) → K = L
  nl : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
    g ∈ Subgroup.normalizer (L : Set G)

theorem setting_of (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M)
    (hn : 1 < E3.mQuot V U) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hLM : ¬ L ≤ M) (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1) :
    Setting M V U L := by
  classical
  have hV := h.isElemAbelian
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hUV : U ≤ V := hU.1
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hCVM : Subgroup.centralizer (V : Set G) ≤ M := h.centralizer_le
  have hNH : ∀ g ∈ Subgroup.normalizer (U : Set G), g ∈ Subgroup.normalizer (H : Set G) :=
    fun g hg => B2F.le_normalizer_centralizer le_rfl hg
  have hLH : L ≤ H := hL.1
  have hCL : V ⊓ Subgroup.centralizer (L : Set G) = U := by
    have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun l hl =>
        (Subgroup.mem_centralizer_iff.1 (hLH hl) u hu).symm
    by_contra hne
    have hlt : U < V ⊓ Subgroup.centralizer (L : Set G) := lt_of_le_of_ne hUC (Ne.symm hne)
    apply hLM
    refine le_trans (fun l hl => ?_) (hmax _ hlt inf_le_left)
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := fun v hv =>
    le_normalizer_of_component h hU hL hv
  have hXU : L ⊓ M ≤ Subgroup.centralizer (U : Set G) := inf_le_left.trans hLH
  have hXN : L ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun y hy => hHMN ⟨hLH hy.1, hy.2⟩
  obtain ⟨-, hsup, -⟩ := singer_autI hV hUV hn hXU hXN hcyc hcard
  have hVXL : ⁅V, L ⊓ M⁆ ≤ L := commutator_le_of_normalizes hVN inf_le_left
  have hdich : ∀ g ∈ Subgroup.normalizer (H : Set G),
      CFSG.conjugate L g = L ∨ ⁅L, CFSG.conjugate L g⁆ = ⊥ := fun g hg =>
    (BenderBranch.eq_or_commute_of_isComponentIn hL
      (isComponentIn_conjugate_of_mem_normalizer' hL hg)).imp Eq.symm id
  have hcommfalse : ∀ K : Subgroup G, IsComponentIn K H → ⁅L, K⁆ = ⊥ → False := by
    intro K hK hc
    have hKU : K ≤ H := hK.1
    have hKW : K ≤ Subgroup.centralizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (by rw [Subgroup.commutator_comm]; exact hc)).trans (Subgroup.centralizer_le hVXL)
    have hKV : K ≤ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.le_centralizer_iff, ← hsup]
      exact sup_le (Subgroup.le_centralizer_iff.1 hKU) (Subgroup.le_centralizer_iff.1 hKW)
    exact DoubleA3.not_isComponentIn_of_charTwo (e6_6_one h hUV) _
      (BenderBranch.isComponentIn_of_le hK (le_inf (hKV.trans hCVM) hKU) inf_le_right)
  refine ⟨hL, hLM, hCL, hVN, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLH]
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hy
    rcases hdich y hyN with he | hc
    · exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 he
    · exact (hcommfalse _ (isComponentIn_conjugate_of_mem_normalizer' hL hyN) hc).elim
  · intro K hK
    exact (BenderBranch.eq_or_commute_of_isComponentIn hL hK).elim (fun he => he.symm)
      fun hc => (hcommfalse K hK hc).elim
  · intro g hg hgU
    exact mem_normalizer_of_eq_or_commute hCVM hLH hLM hVXL hsup hg.1 hgU
      (hdich g (hNH g hgU))

end Setting

section Assemble

variable {G : Type} [Group G] [Finite G] {T M V U L X : Subgroup G}

theorem assemble (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hs : Setting M V U L) (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hXLM : X ≤ L ⊓ M) (hXc : IsCyclic ↥X) (hXcard : Nat.card ↥X = 2 ^ E3.mQuot V U - 1)
    (hautX : autI h.isElemAbelian X = autI h.isElemAbelian (L ⊓ M))
    (hNHS : ∀ g ∈ Subgroup.centralizer (U : Set G),
      g ∈ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) → g ∈ Subgroup.normalizer (V : Set G))
    (hthree : Three T M V U L X) : Concl h U L X := by
  classical
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hLH : L ≤ H := hs.comp.1
  have hQH : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) H := e6_5_one h hU
  have hSL : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
    isSylowTwoOf_inf_of_subnormal' hQH hLH hs.comp.2.2
  obtain ⟨hinf2, hsup2, hXLM', hXc', hXcard', hne, hfree, htrans, hnorm, hle⟩ :=
    clause_two h hU hn hXLM hLH hXc hXcard hautX hcyc hcard hs.nl
  have hXL : X ≤ L := fun x hx => (hXLM' hx).1
  have hprod : ((H ⊓ M : Subgroup G) : Set G) * (L : Set G) = (H : Set G) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, l, hl, rfl⟩
      exact H.mul_mem ha.1 (hLH hl)
    · intro g hg
      obtain ⟨l, hl, hn'⟩ := frattini_normalizer hLH hs.ln hSL (H.inv_mem hg)
      have hnH : l⁻¹ * g⁻¹ ∈ H := H.mul_mem (H.inv_mem (hLH hl)) (H.inv_mem hg)
      have hnV := hNHS _ hnH hn'
      have hnM : l⁻¹ * g⁻¹ ∈ M := h.normalizer_le hnV
      refine ⟨(l⁻¹ * g⁻¹)⁻¹, (H ⊓ M).inv_mem ⟨hnH, hnM⟩, l⁻¹, L.inv_mem hl, ?_⟩
      group
  exact ⟨⟨hLH, hs.ln, hprod⟩, ⟨hinf2, hsup2, hXLM', hXc', hXcard', hne, hfree, htrans, hnorm, hle⟩,
    hthree, clause_four h hsup2 hs.vn hXL⟩

end Assemble

section Borel

variable {G : Type} [Group G] [Finite G] {T M V U L X : Subgroup G}

theorem pCoreOf_eq_centerOf (hq : CFSG.IsQuasisimple ↥L)
    (hZ : IsPGroup 2 (Subgroup.center ↥L)) : pCoreOf 2 L = centerOf L := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hq' : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
    have hz' : z ∈ Subgroup.center ↥L :=
      CFSG.RankThreeCoreUniqueness.Helpers.quasisimple_pCore_le_center hq' 2 Nat.prime_two hz
    exact mem_centerOf_iff_center.2 ⟨z, hz', rfl⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_centerOf_iff_center.1 hx
    exact ⟨z, CFSG.LieType.BorelTits.le_pCore 2 inferInstance hZ hz, rfl⟩

theorem commutator_le_left (hXN : X ≤ Subgroup.normalizer (V : Set G)) : ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  rw [commutatorElement_def]
  have := (Subgroup.mem_normalizer_iff.1 (hXN hx) v⁻¹).1 (V.inv_mem hv)
  have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
  rw [e]
  exact V.mul_mem hv this

theorem card_commutator_eq (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hinf : U ⊓ ⁅V, X⁆ = ⊥)
    (hsup : U ⊔ ⁅V, X⁆ = V) : Nat.card ↥⁅V, X⁆ = 2 ^ E3.mQuot V U := by
  have hV := h.isElemAbelian
  have hWV := commutator_le_left (V := V) hXN
  have h1 := card_mul_eq_of_inf_sup hinf hsup
    (fun u hu w hw => B2F.isElemAbelian_comm hV (hU.1 hu) (hWV hw))
  have h2 := E3.card_eq_two_pow_mul h.isPGroup_V hU.1
  rw [h1] at h2
  have hpos : 0 < Nat.card ↥U := Nat.card_pos
  rw [mul_comm] at h2
  exact Nat.eq_of_mul_eq_mul_right hpos h2

theorem three_borel (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hs : Setting M V U L) (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥)
    (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hXLM : X ≤ L ⊓ M) (hXc : IsCyclic ↥X) (hXcard : Nat.card ↥X = 2 ^ E3.mQuot V U - 1)
    (hautX : autI h.isElemAbelian X = autI h.isElemAbelian (L ⊓ M))
    (hZ : IsPGroup 2 (Subgroup.center ↥L))
    (hBor : L ⊓ M = L ⊓ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G))
    (hbar : ∀ P : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf P ⊤ →
      Nat.card (Subgroup.center ↥P) ≤ 2 ^ E3.mQuot V U)
    (hmodel :
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2
          (E3.mQuot V U) ∨
        CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 (E3.mQuot V U) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2
          (E3.mQuot V U) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2
          (E3.mQuot V U)) :
    (∀ g ∈ Subgroup.centralizer (U : Set G),
      g ∈ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) → g ∈ Subgroup.normalizer (V : Set G)) ∧ Three T M V U L X := by
  classical
  have hV := h.isElemAbelian
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set S : Subgroup G := Q ⊓ L with hSdef
  have hUV : U ≤ V := hU.1
  have hLH : L ≤ H := hs.comp.1
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hSL : IsSylowTwoOf S L := isSylowTwoOf_inf_of_subnormal' hQH hLH hs.comp.2.2
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hXH : X ≤ H := fun x hx => hLH (hXLM hx).1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := fun x hx => hHMN ⟨hXH hx, (hXLM hx).2⟩
  have hBN : L ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun y hy => hHMN ⟨hLH hy.1, hy.2⟩
  obtain ⟨hinf2, hsup2, -⟩ := clause_two h hU hn hXLM hLH hXc hXcard hautX hcyc hcard hs.nl
  have hVXL : ⁅V, X⁆ ≤ L := commutator_le_of_normalizes hs.vn (fun x hx => (hXLM hx).1)
  have hWV : ⁅V, X⁆ ≤ V := commutator_le_left hXN
  have hWS : ⁅V, X⁆ ≤ S := le_inf (hWV.trans h.le_inf_centralizer) hVXL
  have hWc : ∀ w ∈ ⁅V, X⁆, ∀ s ∈ S, w * s = s * w := fun w hw s hs' =>
    Subgroup.mem_centralizer_iff.1 (hs'.1.2 : s ∈ Subgroup.centralizer (V : Set G)) w (hWV hw)
  have hcommUW : ∀ u ∈ U, ∀ w ∈ ⁅V, X⁆, u * w = w * u := fun u hu w hw =>
    B2F.isElemAbelian_comm hV (hUV hu) (hWV hw)
  have hWcard := card_commutator_eq h hU hXN hinf2 hsup2
  have hWZ : ∀ w ∈ ⁅V, X⁆, w ∈ centerOf L → w = 1 := by
    intro w hw hwZ
    have h1 : w ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hWV hw, hwZ.2⟩
    rw [hs.cv] at h1
    have h2 : w ∈ U ⊓ ⁅V, X⁆ := ⟨h1, hw⟩
    rw [hinf2, Subgroup.mem_bot] at h2
    exact h2
  have hZS : centerOf S = centerOf L ⊔ ⁅V, X⁆ :=
    centerOf_sylow_eq_sup hSL hZ hbar hWS hWc hWcard hWZ
  have hWnB : ∀ b ∈ L ⊓ M, b ∈ Subgroup.normalizer ((⁅V, X⁆ : Subgroup G) : Set G) := by
    intro b hb
    have hWeq : ⁅V, X⁆ = ⁅V, L ⊓ M⁆ := commutator_eq_of_autI_eq hV hXLM hBN hautX
    rw [hWeq]
    exact mem_normalizer_commutator (hBN hb) (Subgroup.le_normalizer hb)
  have hXU : ∀ x ∈ X, ∀ u ∈ U, x * u = u * x := fun x hx u hu =>
    (Subgroup.mem_centralizer_iff.1 (hXH hx) u hu).symm
  have hD : ⁅centerOf S, L ⊓ Subgroup.normalizer (S : Set G)⁆ = ⁅V, X⁆ := by
    rw [← hBor]
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro z hz b hb
      rw [hZS] at hz
      have hcen : centerOf L ≤ Subgroup.normalizer ((⁅V, X⁆ : Subgroup G) : Set G) :=
        le_normalizer_of_commute fun a ha w hw =>
          (Subgroup.mem_centralizer_iff.1 ha.2 w (hVXL hw)).symm
      have hzmem : z ∈ ((centerOf L : Subgroup G) : Set G) * ((⁅V, X⁆ : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right (centerOf L) ⁅V, X⁆ hcen]
        exact hz
      obtain ⟨c, hc, w', hw', rfl⟩ := hzmem
      have hcb : Commute c b := (Subgroup.mem_centralizer_iff.1 hc.2 b hb.1).symm
      have hcw : Commute c w' := (Subgroup.mem_centralizer_iff.1 hc.2 w' (hVXL hw')).symm
      have hcom : c * (w' * b * w'⁻¹) = (w' * b * w'⁻¹) * c :=
        ((hcw.mul_right hcb).mul_right hcw.inv_right).eq
      have hb' : b * w'⁻¹ * b⁻¹ ∈ ⁅V, X⁆ :=
        (Subgroup.mem_normalizer_iff.1 (hWnB b hb) w'⁻¹).1 (⁅V, X⁆.inv_mem hw')
      have : ⁅c * w', b⁆ = w' * (b * w'⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]
        calc c * w' * b * (c * w')⁻¹ * b⁻¹ = c * (w' * b * w'⁻¹) * c⁻¹ * b⁻¹ := by group
          _ = (w' * b * w'⁻¹) * c * c⁻¹ * b⁻¹ := by rw [hcom]
          _ = w' * (b * w'⁻¹ * b⁻¹) := by group
      rw [this]
      exact ⁅V, X⁆.mul_mem hw' hb'
    · calc ⁅V, X⁆ ≤ ⁅(⁅V, X⁆ : Subgroup G), X⁆ := commutator_le_of_sup hsup2 hcommUW hXU
        _ ≤ ⁅centerOf S, L ⊓ M⁆ := Subgroup.commutator_mono
            (fun w hw => ⟨hWS hw, Subgroup.mem_centralizer_iff.2 fun s hs' => (hWc w hw s hs').symm⟩)
            hXLM
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hs.ln
  have hHU : ∀ g ∈ H, ∀ u ∈ U, g * u = u * g := fun g hg u hu =>
    (Subgroup.mem_centralizer_iff.1 hg u hu).symm
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hs.comp
  refine ⟨fun g hg hgS => normalizer_le_of_lin hHL hHU hsup2 hD hg hgS,
    Or.inr (Or.inl ⟨?_, hmodel, ?_, ?_⟩)⟩
  · exact generalizedFitting_eq_of_unique_component hs.comp hs.uniq hO
  · exact ⟨S, hSL, by rw [inf_comm, hBor]⟩
  · rw [pCoreOf_eq_centerOf hq hZ, inf_comm L]
    exact hZS.symm

end Borel

section Sp4

variable {G : Type} [Group G] [Finite G] {T M V U L X : Subgroup G}

theorem perfect_le_centralizer (hV : IsElemAbelian 2 V) {P C : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (V : Set G)) (hcyc : IsCyclic ↥(autI hV P)) (hCP : C ≤ P)
    (hC : ⁅C, C⁆ = C) : C ≤ Subgroup.centralizer (V : Set G) := by
  calc C = ⁅C, C⁆ := hC.symm
    _ ≤ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.commutator_le]
      intro c₁ h₁ c₂ h₂
      have hn₁ : c₁ ∈ Subgroup.normalizer (V : Set G) := hPN (hCP h₁)
      have hn₂ : c₂ ∈ Subgroup.normalizer (V : Set G) := hPN (hCP h₂)
      have hcomm : convI hV ⟨c₁, hn₁⟩ * convI hV ⟨c₂, hn₂⟩ =
          convI hV ⟨c₂, hn₂⟩ * convI hV ⟨c₁, hn₁⟩ :=
        E6.E68Proof.RankOne.commute_of_cyclic hcyc (convI_mem_autI hV (hCP h₁) hn₁)
          (convI_mem_autI hV (hCP h₂) hn₂)
      have hmem : ⁅c₁, c₂⁆ ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₁ hn₂)
          (Subgroup.inv_mem _ hn₁)) (Subgroup.inv_mem _ hn₂)
      refine (convI_eq_one_iff hV ⟨⁅c₁, c₂⁆, hmem⟩).1 ?_
      have : (⟨⁅c₁, c₂⁆, hmem⟩ : Subgroup.normalizer (V : Set G)) =
          ⁅(⟨c₁, hn₁⟩ : Subgroup.normalizer (V : Set G)), ⟨c₂, hn₂⟩⁆ := rfl
      rw [this, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm

theorem three_sp4 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hs : Setting M V U L) (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥)
    (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 (E3.mQuot V U))
    (hPS : L ⊓ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G) ≤ L ⊓ M)
    (hPlt : L ⊓ M < L)
    (hPmax : ∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) :
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧ IsCyclic ↥X ∧ Nat.card ↥X = 2 ^ E3.mQuot V U - 1 ∧
      autI h.isElemAbelian X = autI h.isElemAbelian (L ⊓ M) ∧
      (∀ g ∈ Subgroup.centralizer (U : Set G),
        g ∈ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
          Set G) → g ∈ Subgroup.normalizer (V : Set G)) ∧ Three T M V U L X := by
  classical
  have hV := h.isElemAbelian
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set S : Subgroup G := Q ⊓ L with hSdef
  set P := L ⊓ M with hPdef
  have hUV : U ≤ V := hU.1
  have hLH : L ≤ H := hs.comp.1
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hSL : IsSylowTwoOf S L := isSylowTwoOf_inf_of_subnormal' hQH hLH hs.comp.2.2
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := fun y hy => hHMN ⟨hLH hy.1, hy.2⟩
  have hPH : P ≤ H := inf_le_left.trans hLH
  obtain ⟨hinf, hsup, -⟩ := singer_autI hV hUV hn (fun x hx => hPH hx) hPN hcyc hcard
  have hVPL : ⁅V, P⁆ ≤ L := commutator_le_of_normalizes hs.vn inf_le_left
  have hWV : ⁅V, P⁆ ≤ V := commutator_le_left hPN
  have hWS : ⁅V, P⁆ ≤ S := le_inf (hWV.trans h.le_inf_centralizer) hVPL
  have hWc : ∀ w ∈ ⁅V, P⁆, ∀ s ∈ S, w * s = s * w := fun w hw s hs' =>
    Subgroup.mem_centralizer_iff.1 (hs'.1.2 : s ∈ Subgroup.centralizer (V : Set G)) w (hWV hw)
  have hW2 : ∀ w ∈ ⁅V, P⁆, w * w = 1 := fun w hw => by
    have := F7.isElemAbelian_pow_eq_one hV (hWV hw)
    rwa [pow_two] at this
  have hWcard : Nat.card ↥⁅V, P⁆ = 2 ^ E3.mQuot V U := card_commutator_eq h hU hPN hinf hsup
  have hWn : ∀ p ∈ P, ∀ w ∈ ⁅V, P⁆, p * w * p⁻¹ ∈ ⁅V, P⁆ := fun p hp w hw =>
    (Subgroup.mem_normalizer_iff.1
      (mem_normalizer_commutator (hPN hp) (Subgroup.le_normalizer hp)) w).1 hw
  obtain ⟨K, _, _, _, φ, hK, hφ⟩ := Sp4G.exists_adapted hn hmodel hSL
  have hn2 : 2 ≤ E3.mQuot V U := hn
  obtain ⟨i, hWi, hPi, hroot, hCP, hperf, X₀, hX₀P, hX₀c, hX₀card, hX₀dec⟩ :=
    Sp4G.parabolic hn2 hK hφ hSL inf_le_left hPS (ne_of_lt hPlt) hPmax hWS hWc hWn hW2 hWcard
  have hCP' : L ⊓ Subgroup.centralizer ((⁅V, P⁆ : Subgroup G) : Set G) ≤ P := fun g hg =>
    hCP g hg.1 (fun w hw => (Subgroup.mem_centralizer_iff.1 hg.2 w hw).symm)
  have hCV : L ⊓ Subgroup.centralizer ((⁅V, P⁆ : Subgroup G) : Set G) ≤
      Subgroup.centralizer (V : Set G) := perfect_le_centralizer hV hPN hcyc hCP' hperf
  have hautX : autI hV X₀ = autI hV P := by
    refine autI_eq_of_surj hV hPN hX₀P (fun a ha => ?_)
    obtain ⟨p, rfl⟩ := ha
    obtain ⟨c, hc, x₀, hx₀, hpeq⟩ := hX₀dec p p.2
    have hcP : c ∈ P := hCP' hc
    refine ⟨⟨x₀, hX₀P hx₀⟩, hx₀, ?_⟩
    have hpp : p = ⟨c, hcP⟩ * ⟨x₀, hX₀P hx₀⟩ := Subtype.ext hpeq
    rw [hpp, map_mul]
    have h1 : convHom hV P hPN ⟨c, hcP⟩ = 1 := (convI_eq_one_iff hV ⟨c, hPN hcP⟩).2 (hCV hc)
    rw [h1, one_mul]
  have hWX : ⁅V, X₀⁆ = ⁅V, P⁆ := commutator_eq_of_autI_eq hV hX₀P hPN hautX
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hs.ln
  have hHU : ∀ g ∈ H, ∀ u ∈ U, g * u = u * g := fun g hg u hu =>
    (Subgroup.mem_centralizer_iff.1 hg u hu).symm
  have hQN : Q ≤ Subgroup.normalizer (S : Set G) := fun q hq =>
    mem_normalizer_inf (Subgroup.le_normalizer hq) (hHL (hQH.1 hq))
  have hQSyl : IsSylowTwoOf Q (H ⊓ Subgroup.normalizer (S : Set G)) :=
    isSylowTwoOf_of_le hQH (le_inf hQH.1 hQN) inf_le_left
  have hQW : Q ≤ Subgroup.normalizer ((⁅V, P⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun a ha w hw =>
      (Subgroup.mem_centralizer_iff.1 ha.2 w (hWV hw)).symm
  have hBW : ∀ b ∈ L ⊓ Subgroup.normalizer (S : Set G), ∀ w ∈ ⁅V, P⁆, b * w * b⁻¹ ∈ ⁅V, P⁆ :=
    fun b hb w hw => hWn b (hPS hb) w hw
  have hNHS : ∀ g ∈ H, g ∈ Subgroup.normalizer (S : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) := fun g hg hgS =>
    normalizer_le_of_two_roots (W₁ := (CFSG.Quasithin.SteinbergBS.rootShort K).map (Sp4G.emb φ))
      (W₂ := (CFSG.Quasithin.SteinbergBS.rootLong K).map (Sp4G.emb φ)) hHL hHU hsup hQSyl hQW
      (fun W' h1 h2 h3 h4 => Sp4G.eq_roots_of_central hn2 hK hφ hSL.1 h1 h2 h3
        (h4.trans hWcard)) hWS hWc hBW hg hgS
  refine ⟨X₀, hX₀P, hX₀c, hX₀card, hautX, hNHS, Or.inr (Or.inr ⟨?_, hmodel, ?_, ?_, ?_⟩)⟩
  · exact generalizedFitting_eq_of_unique_component hs.comp hs.uniq hO
  · refine ⟨⟨inf_le_left, S, hSL, hPS⟩, ne_of_lt hPlt, ?_⟩
    intro Q' hQ'par hQ'ne hPQ'
    rcases hPmax Q' hPQ' hQ'par.1 with he | he
    · exact he
    · exact absurd he hQ'ne
  · apply le_antisymm
    · have h1 := perfectCore_le P
      have h2 := perfectCore_perfect P
      exact le_inf (h1.trans inf_le_left) (perfect_le_centralizer hV hPN hcyc h1 h2)
    · have hC : L ⊓ Subgroup.centralizer (V : Set G) =
          L ⊓ Subgroup.centralizer ((⁅V, P⁆ : Subgroup G) : Set G) :=
        le_antisymm (inf_le_inf_left L (Subgroup.centralizer_le hWV)) (le_inf inf_le_left hCV)
      rw [hC]
      exact le_perfectCore_of_perfect hCP' hperf
  · rw [hWX]
    exact hroot.symm

end Sp4

section Cases

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem cv_eq (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hLM : ¬ L ≤ M) :
    V ⊓ Subgroup.centralizer (L : Set G) = U := by
  have hUV : U ≤ V := hU.1
  have hLH : L ≤ Subgroup.centralizer (U : Set G) := hL.1
  have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hLH hl) u hu).symm
  by_contra hne
  have hlt : U < V ⊓ Subgroup.centralizer (L : Set G) := lt_of_le_of_ne hUC (Ne.symm hne)
  apply hLM
  refine le_trans (fun l hl => ?_) (hmax _ hlt inf_le_left)
  exact Subgroup.mem_centralizer_iff.2 fun w hw =>
    (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm

theorem concl_of_bender (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hBK : E68BorelKernel) (hs : Setting M V U L)
    (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥)
    (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hZ : IsPGroup 2 (Subgroup.center ↥L))
    (hBor : L ⊓ M = L ⊓ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G))
    (hmodel : E611TypeBender L (E3.mQuot V U)) : ∃ X : Subgroup G, Concl h U L X := by
  classical
  have hV := h.isElemAbelian
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hLH : L ≤ H := hs.comp.1
  have hQH : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) H := e6_5_one h hU
  have hSL : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
    isSylowTwoOf_inf_of_subnormal' hQH hLH hs.comp.2.2
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hBN : L ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun y hy => hHMN ⟨hLH hy.1, hy.2⟩
  have hker := not_dvd_card_inf_centralizer_of_borel hBK hV hn hmodel hZ hSL hBor hBN hcard
  obtain ⟨X, hXLM, hXc, hXcard, hautX⟩ := exists_X_of_coprime hV hBN hcyc
    (fun p hp hpd => hker p hp (hcard ▸ hpd))
  rw [hcard] at hXcard
  obtain ⟨k', hk'⟩ : ∃ k', E6.E68Proof.ModelOf (↥L ⧸ Subgroup.center ↥L) (2 ^ E3.mQuot V U) k' := by
    rcases hmodel with h1 | h2 | h3
    · exact ⟨1, E6.E68Proof.modelOf_of_stated_psl hn h1⟩
    · exact ⟨2, E6.E68Proof.modelOf_of_suzuki h2⟩
    · exact ⟨3, E6.E68Proof.modelOf_of_stated_psu hn h3⟩
  have hbar : ∀ P : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf P ⊤ →
      Nat.card (Subgroup.center ↥P) ≤ 2 ^ E3.mQuot V U := fun P hP =>
    (card_center_sylow_modelOf hk' hP).le
  have hmodel4 :
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2
          (E3.mQuot V U) ∨
        CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 (E3.mQuot V U) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2
          (E3.mQuot V U) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2
          (E3.mQuot V U) := by
    rcases hmodel with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr h3))
  obtain ⟨hNHS, hthree⟩ := three_borel h hU hn hs hO hcyc hcard hXLM hXc hXcard hautX hZ hBor
    hbar hmodel4
  exact ⟨X, assemble h hU hn hs hcyc hcard hXLM hXc hXcard hautX hNHS hthree⟩

theorem concl_of_lin3 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hs : Setting M V U L) (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥)
    (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hZ : IsPGroup 2 (Subgroup.center ↥L))
    (hBor : L ⊓ M = L ⊓ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G))
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2
      (E3.mQuot V U)) : ∃ X : Subgroup G, Concl h U L X := by
  classical
  have hV := h.isElemAbelian
  have hn2 : 2 ≤ E3.mQuot V U := hn
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hLH : L ≤ H := hs.comp.1
  have hQH : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) H := e6_5_one h hU
  have hSL : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
    isSylowTwoOf_inf_of_subnormal' hQH hLH hs.comp.2.2
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hBN : L ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun y hy => hHMN ⟨hLH hy.1, hy.2⟩
  have hodd : Odd (Nat.card ↥(autI hV (L ⊓ M))) := by
    rw [hcard]
    have h4 : 4 ≤ 2 ^ E3.mQuot V U :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hn
    have he : Even (2 ^ E3.mQuot V U) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd (by omega) he odd_one
  obtain ⟨X, hXLM, hXc, hXcard, hautX⟩ := exists_X_of_exponent hV (le_refl (L ⊓ M)) hBN hcyc hodd
    rfl (fun g hg => by
      rw [hcard]
      have hg' : g ∈ L ⊓ Subgroup.normalizer
          (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G) := hBor ▸ hg
      exact exists_pow_eq_one_of_lin3 hn2 hmodel hZ hSL hg')
  rw [hcard] at hXcard
  have hbar : ∀ P : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf P ⊤ →
      Nat.card (Subgroup.center ↥P) ≤ 2 ^ E3.mQuot V U := fun P hP =>
    card_center_sylow_le_lin3 hn2 hmodel hP
  obtain ⟨hNHS, hthree⟩ := three_borel h hU hn hs hO hcyc hcard hXLM hXc hXcard hautX hZ hBor
    hbar (Or.inr (Or.inr (Or.inl hmodel)))
  exact ⟨X, assemble h hU hn hs hcyc hcard hXLM hXc hXcard hautX hNHS hthree⟩

theorem concl_of_sp4 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hn : 1 < E3.mQuot V U)
    (hs : Setting M V U L) (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥)
    (hcyc : IsCyclic (autI h.isElemAbelian (L ⊓ M)))
    (hcard : Nat.card (autI h.isElemAbelian (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 (E3.mQuot V U))
    (hPS : L ⊓ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G) ≤ L ⊓ M)
    (hPlt : L ⊓ M < L)
    (hPmax : ∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) :
    ∃ X : Subgroup G, Concl h U L X := by
  obtain ⟨X, hXLM, hXc, hXcard, hautX, hNHS, hthree⟩ :=
    three_sp4 h hU hn hs hO hcyc hcard hmodel hPS hPlt hPmax
  exact ⟨X, assemble h hU hn hs hcyc hcard hXLM hXc hXcard hautX hNHS hthree⟩

end Cases

end CFSG.Quasithin.RonanE611
