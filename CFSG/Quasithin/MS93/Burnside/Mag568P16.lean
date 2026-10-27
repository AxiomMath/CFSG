module

public import CFSG.Quasithin.MS93.Burnside.Mag568Coord
public import CFSG.Quasithin.MS93.S34FGC

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideMag568_le_commutator_qv (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hbad : mag568_Bad h)
    {E : Subgroup (puAmalgam h.le).Universal} (hEf : E ≤ S34F.flat h (baseA _))
    (hcard : Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
        Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le))))
    (hZT : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer
      ((Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal))
    (hRG : mag568_RG h (Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)))
    {α : Vtx (puAmalgam h.le)} (hα : (puAmalgam h.le).treeGraph.Adj (baseB _) α)
    (hZQ : ⁅Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal), Qv (puAmalgam h.le) α⁆ ≠ ⊥) :
    Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      ⁅Uloc h.le L (baseA (puAmalgam h.le)), Qv (puAmalgam h.le) α⁆ := by
  have h20 := h.hyp20
  have hC := h.centHyp
  have hb0 := h.critDist_pos
  have hα₀ := PU.isMVtx_baseA (puAmalgam h.le)
  have hα₀β := adj_baseA_baseB (puAmalgam h.le)
  have hαM : IsMVtx _ α := by
    have h1 := isMVtx_iff_of_adj _ hα
    have h2 := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  obtain ⟨n, F, _, _, φ, hcardF, hφs, hnat⟩ := exists_natural_flat h hU
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcardF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_flat_at h hφs hnat hα₀
  set U := Uloc h.le L (baseA (puAmalgam h.le)) with hUdef
  set Z := U ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) with hZdef
  set Q := Qv (puAmalgam h.le) α with hQdef
  set X := ⁅U, Q⁆ with hXdef
  have hβs : Qv (puAmalgam h.le) (baseB _) ≤ stab _ (baseA _) := qv_le_stab_of_adj _ hα₀β.symm
  have hQβ : Q ≤ Qv _ (baseB _) := qv_le_qv _ h20 hαM hα.symm
  have hβU : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (U : Set _) :=
    hβs.trans (S4A.stab_le_normalizer_uloc h _)
  have hβf : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (S34F.flat h (baseA _) : Set _) :=
    hβs.trans (stab_le_normalizer_puTrans h.le (flat_subgroupOf_normal h) _)
  have hβQ : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (Q : Set _) :=
    (qv_le_stab_of_adj _ hα).trans (stab_le_normalizer_qv _ α)
  have hXU : X ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp (hQβ.trans hβU)
  have hβX : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (X : Set _) :=
    le_normalizer_commutator hβU hβQ
  have hZQZ : ⁅Z, Q⁆ ≤ Z := Subgroup.le_normalizer_iff_commutator_le_left.mp (hQβ.trans hZT)
  have hZQX : ⁅Z, Q⁆ ≤ X := Subgroup.commutator_mono inf_le_left le_rfl
  have hℓ : Module.finrank F (fixN (natImage ψ E)) = 1 :=
    burnsideMag568_finrank_fixN_eq_one hψ hEf hcard
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ ⁅Z, Q⁆, z₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hZQ
    rw [eq_bot_iff]
    intro z hz
    exact (Subgroup.mem_bot).mpr (hall z hz)
  have hz₀U : z₀ ∈ U := (hZQZ hz₀).1
  set z₀' : ↥U := ⟨z₀, hz₀U⟩ with hz₀'def
  have hz₀f : natVec hψ z₀' ∈ fixN (natImage ψ E) :=
    (burnsideMag568_mem_centralizer_iff hψ hEf z₀').mp (hZQZ hz₀).2
  have hz₀0 : natVec hψ z₀' ≠ 0 := fun h0 =>
    hz₀1 (congrArg Subtype.val (natVec_injective hψ (h0.trans (natVec_one hψ).symm)))
  have hline : ∀ w : ↥U, (w : (puAmalgam h.le).Universal) ∈ Subgroup.centralizer (E : Set _) →
      ∃ c : F, natVec hψ w = c • natVec hψ z₀' := by
    intro w hw
    have hwf := (burnsideMag568_mem_centralizer_iff hψ hEf w).mp hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hz₀f⟩ : fixN (natImage ψ E))
      (fun h0 => hz₀0 (congrArg Subtype.val h0))).mp hℓ ⟨_, hwf⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  by_cases hlin : ∀ x ∈ Q, ∀ f : (Fin 3 → F) → (Fin 3 → F),
      (∀ v v' : ↥U, (v' : (puAmalgam h.le).Universal) = x * v * x⁻¹ →
        natVec hψ v' = f (natVec hψ v)) →
      ∀ (c : F) (y : Fin 3 → F), f (c • y) = c • f y
  ·
    have hsc : ∀ y ∈ X, ∃ hy : y ∈ U, ∀ c : F, ∃ w : ↥U,
        (w : (puAmalgam h.le).Universal) ∈ X ∧ natVec hψ w = c • natVec hψ ⟨y, hy⟩ := by
      intro y hy
      rw [hXdef, Subgroup.commutator_def] at hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨u, hu, x, hx, rfl⟩ := hy
        refine ⟨hXU (Subgroup.commutator_mem_commutator hu hx), fun c => ?_⟩
        have hxU := hQβ.trans hβU hx
        obtain ⟨f, σ, hf, -⟩ := exists_semilinear_natVec hψs hψ hxU (hQβ.trans hβf hx)
        have hfl := hlin x hx f hf
        obtain ⟨u', hu'⟩ := natVec_surjective hψ (c • natVec hψ ⟨u, hu⟩)
        have hmem : ⁅(u' : (puAmalgam h.le).Universal), x⁆ ∈ X :=
          Subgroup.commutator_mem_commutator u'.2 hx
        refine ⟨⟨_, hXU hmem⟩, hmem, ?_⟩
        have hxu' : x * u' * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU u').mp u'.2
        have hxu : x * u * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU u).mp hu
        rw [burnsideMag568_natVec_commutator_of_normalizer hψ u' ⟨_, hxu'⟩ ⟨_, hXU hmem⟩ rfl rfl,
          burnsideMag568_natVec_commutator_of_normalizer hψ ⟨u, hu⟩ ⟨_, hxu⟩
            ⟨_, hXU (Subgroup.commutator_mem_commutator hu hx)⟩ rfl rfl,
          hf u' ⟨_, hxu'⟩ rfl, hf ⟨u, hu⟩ ⟨_, hxu⟩ rfl, hu', hfl, smul_sub]
      | one =>
        refine ⟨U.one_mem, fun c => ⟨1, X.one_mem, ?_⟩⟩
        rw [show (⟨1, U.one_mem⟩ : ↥U) = 1 from rfl, natVec_one, smul_zero]
      | mul a b _ _ iha ihb =>
        obtain ⟨ha, ha'⟩ := iha
        obtain ⟨hb', hb''⟩ := ihb
        refine ⟨U.mul_mem ha hb', fun c => ?_⟩
        obtain ⟨w₁, hw₁X, hw₁⟩ := ha' c
        obtain ⟨w₂, hw₂X, hw₂⟩ := hb'' c
        refine ⟨w₁ * w₂, X.mul_mem hw₁X hw₂X, ?_⟩
        rw [natVec_mul, hw₁, hw₂, show (⟨a * b, U.mul_mem ha hb'⟩ : ↥U) = ⟨a, ha⟩ * ⟨b, hb'⟩ from rfl,
          natVec_mul, smul_add]
      | inv a _ iha =>
        obtain ⟨ha, ha'⟩ := iha
        refine ⟨U.inv_mem ha, fun c => ?_⟩
        obtain ⟨w₁, hw₁X, hw₁⟩ := ha' c
        refine ⟨w₁⁻¹, X.inv_mem hw₁X, ?_⟩
        rw [natVec_inv, hw₁, show (⟨a⁻¹, U.inv_mem ha⟩ : ↥U) = (⟨a, ha⟩ : ↥U)⁻¹ from rfl,
          natVec_inv, smul_neg]
    intro w hw
    obtain ⟨c, hc⟩ := hline ⟨w, hw.1⟩ hw.2
    obtain ⟨_, hsc0⟩ := hsc z₀ (hZQX hz₀)
    obtain ⟨w', hw'X, hw'⟩ := hsc0 c
    have heq : w' = ⟨w, hw.1⟩ := natVec_injective hψ (hw'.trans hc.symm)
    have : (w' : (puAmalgam h.le).Universal) = w := congrArg Subtype.val heq
    rw [← this]
    exact hw'X
  ·
    push Not at hlin
    obtain ⟨x, hx, f, hf, c, y, hcy⟩ := hlin
    have hxU := hQβ.trans hβU hx
    obtain ⟨f', σ, hf', hσ⟩ := exists_semilinear_natVec hψs hψ hxU (hQβ.trans hβf hx)
    have hff : ∀ y, f y = f' y := by
      intro y
      obtain ⟨v, rfl⟩ := natVec_surjective hψ y
      have hxv : x * v * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU v).mp v.2
      rw [← hf v ⟨_, hxv⟩ rfl, ← hf' v ⟨_, hxv⟩ rfl]
    have hσc : σ c ≠ c := by
      intro he
      apply hcy
      rw [hff, hff, hσ, he]
    have hnot : ∀ W : Submodule F (Fin 3 → F), W ≠ ⊤ →
        ∃ v : ↥U, (v : (puAmalgam h.le).Universal) ∈ X ∧ natVec hψ v ∉ W := by
      intro W hW
      by_contra hall
      push Not at hall
      apply hW
      refine burnsideMag568_eq_top_of_sub_mem (f := f') (σ := σ) hσ hσc fun y => ?_
      obtain ⟨v, rfl⟩ := natVec_surjective hψ y
      have hxv : x * v * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU v).mp v.2
      have hmem : ⁅(v : (puAmalgam h.le).Universal), x⁆ ∈ X :=
        Subgroup.commutator_mem_commutator v.2 hx
      have := hall ⟨_, hXU hmem⟩ hmem
      rwa [burnsideMag568_natVec_commutator_of_normalizer hψ v ⟨_, hxv⟩ ⟨_, hXU hmem⟩ rfl rfl,
        hf' v ⟨_, hxv⟩ rfl] at this
    obtain ⟨μ, hcμ, hμβ, hRG'⟩ := hRG
    have hμM := hcμ.isMVtx_right _ h20
    have hZμf : ZM (puAmalgam h.le) μ ≤ S34F.flat h (baseA _) :=
      zm_le_flat h hU (ms22_iii _ h20 hb0 hC hcμ)
    obtain ⟨hf2, hw1, hcardμ⟩ :=
      burnsideMag568_rootGroup h hU hb hcardF hφs hnat hcμ (hbad μ hμM) hψ
    have hcardμ' : Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) μ)) =
        Nat.card ↥(commN (natImage ψ (ZM (puAmalgam h.le) μ))) := by
      rw [hcardμ, Module.natCard_eq_pow_finrank (K := F)
        (V := commN (natImage ψ (ZM (puAmalgam h.le) μ))), hw1, pow_one]
    have hWtop : ∀ μ₁ : Vtx (puAmalgam h.le),
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) μ₁))) = 2 →
        fixN (natImage ψ (ZM (puAmalgam h.le) μ₁)) ≠ ⊤ := by
      intro μ₁ h2 htop
      rw [htop, finrank_top, Module.finrank_fin_fun] at h2
      omega
    obtain ⟨v, hvX, hvW⟩ := hnot _ (hWtop μ hf2)
    have hvC : (v : (puAmalgam h.le).Universal) ∉
        Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) := fun hc =>
      hvW ((burnsideMag568_mem_centralizer_iff hψ hZμf v).mp hc)
    have hRμ : ⁅U, ZM (puAmalgam h.le) μ⁆ ≤ X :=
      burnsideMag568_le_of_orbit hψ hZμf (hμβ.trans hβX) hXU hf2 hcardμ' hvX hvC
    rcases hRG' with hR | ⟨μ', hcμ', hμ'β, hW, hZW, hne⟩
    · rw [← hR]
      exact hRμ
    · have hμ'M := hcμ'.isMVtx_right _ h20
      have hZμ'f : ZM (puAmalgam h.le) μ' ≤ S34F.flat h (baseA _) :=
        zm_le_flat h hU (ms22_iii _ h20 hb0 hC hcμ')
      obtain ⟨hf2', hw1', hcardμ''⟩ :=
        burnsideMag568_rootGroup h hU hb hcardF hφs hnat hcμ' (hbad μ' hμ'M) hψ
      have hcard' : Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) μ')) =
          Nat.card ↥(commN (natImage ψ (ZM (puAmalgam h.le) μ'))) := by
        rw [hcardμ'', Module.natCard_eq_pow_finrank (K := F)
          (V := commN (natImage ψ (ZM (puAmalgam h.le) μ'))), hw1', pow_one]
      have hvC' : (v : (puAmalgam h.le).Universal) ∉
          Subgroup.centralizer (ZM (puAmalgam h.le) μ' : Set _) := by
        intro hc'
        apply hvC
        have hmem : (v : (puAmalgam h.le).Universal) ∈
            U ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) μ' : Set _) := ⟨v.2, hc'⟩
        rw [← hW] at hmem
        exact hmem.2
      have hRμ' : ⁅U, ZM (puAmalgam h.le) μ'⁆ ≤ X :=
        burnsideMag568_le_of_orbit hψ hZμ'f (hμ'β.trans hβX) hXU hf2' hcard' hvX hvC'
      have hfixeq : fixN (natImage ψ (ZM (puAmalgam h.le) μ')) =
          fixN (natImage ψ (ZM (puAmalgam h.le) μ)) := by
        ext y
        obtain ⟨u, rfl⟩ := natVec_surjective hψ y
        rw [← burnsideMag568_mem_centralizer_iff hψ hZμf u,
          ← burnsideMag568_mem_centralizer_iff hψ hZμ'f u]
        constructor
        · intro h1
          have hmem : (u : (puAmalgam h.le).Universal) ∈
              U ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) μ' : Set _) := ⟨u.2, h1⟩
          rw [← hW] at hmem
          exact hmem.2
        · intro h1
          have hmem : (u : (puAmalgam h.le).Universal) ∈
              U ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) := ⟨u.2, h1⟩
          rw [hW] at hmem
          exact hmem.2
      have hcommle : commN (natImage ψ (ZM (puAmalgam h.le) μ)) ≤
          fixN (natImage ψ (ZM (puAmalgam h.le) μ)) :=
        commN_le_fixN_of_elemAb (natImage_zm_sq h hμM) (natImage_zm_comm h hμM)
      have hcommle' : commN (natImage ψ (ZM (puAmalgam h.le) μ')) ≤
          fixN (natImage ψ (ZM (puAmalgam h.le) μ)) :=
        hfixeq ▸ commN_le_fixN_of_elemAb (natImage_zm_sq h hμ'M) (natImage_zm_comm h hμ'M)
      have hUμ : ⁅U, ZM (puAmalgam h.le) μ⁆ ≤ U :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hZμf.trans hψ.1)
      have hUμ' : ⁅U, ZM (puAmalgam h.le) μ'⁆ ≤ U :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hZμ'f.trans hψ.1)
      have hcne : commN (natImage ψ (ZM (puAmalgam h.le) μ)) ≠
          commN (natImage ψ (ZM (puAmalgam h.le) μ')) := by
        intro he
        apply hne
        ext w
        constructor
        · intro hw
          have h1 := (burnsideMag568_mem_commutator_iff hψ hZμf ⟨w, hUμ hw⟩).mp hw
          rw [he] at h1
          exact (burnsideMag568_mem_commutator_iff hψ hZμ'f ⟨w, hUμ hw⟩).mpr h1
        · intro hw
          have h1 := (burnsideMag568_mem_commutator_iff hψ hZμ'f ⟨w, hUμ' hw⟩).mp hw
          rw [← he] at h1
          exact (burnsideMag568_mem_commutator_iff hψ hZμf ⟨w, hUμ' hw⟩).mpr h1
      have hsup := burnsideMag568_sup_eq_of_ne hw1 hw1' hf2 hcommle hcommle' hcne
      intro w hw
      have hwW : natVec hψ ⟨w, hw.1⟩ ∈ fixN (natImage ψ (ZM (puAmalgam h.le) μ)) :=
        (burnsideMag568_mem_centralizer_iff hψ hZμf ⟨w, hw.1⟩).mp (hZW hw).2
      rw [← hsup] at hwW
      exact (sup_le hRμ hRμ') (burnsideMag568_mem_sup_of_natVec hψ hZμf hZμ'f ⟨w, hw.1⟩ hwW)

end CFSG.Quasithin.MS93.S4L
