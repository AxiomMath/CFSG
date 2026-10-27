module

public import CFSG.RankThree.GF2n.Tim79aIdentCore
public import CFSG.RankThree.GF2n.Tim79aTransvectionHyp
public import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection

@[expose] def TransvectionGenerationStatement : Prop :=
  ∀ (K : Type) [Group K] (Δ : Set (Subgroup K)), TransvectionHyp K Δ →
    (∀ A ∈ Δ, 4 ≤ Nat.card A) → ∀ A ∈ Δ, ∀ B ∈ Δ, Opposite A B → ∀ b ∈ B, b ≠ 1 →
      (⨆ C ∈ Δ, ⨆ (_ : C ≤ Subgroup.centralizer (A : Set K)), C) ⊔ Subgroup.zpowers b = ⊤

@[expose] def TransvectionTorusStatement : Prop :=
  ∀ (K : Type) [Group K] (Δ : Set (Subgroup K)), TransvectionHyp K Δ →
    (∀ A ∈ Δ, 4 ≤ Nat.card A) → ∀ A ∈ Δ, ∀ E : Subgroup K, E ≤ A → E ≠ ⊥ →
      ⨆ n ∈ Subgroup.normalizer (A : Set K), conjSub E n = A

variable {G : Type} [Group G]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem vtilde_eq_of_le (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hG : TransvectionGenerationStatement) (hTor : TransvectionTorusStatement)
    {Δ : Set (Subgroup (XbarZ V H))}
    (hΔ : TransvectionHyp (XbarZ V H) Δ) (h4 : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {A₀ : Subgroup (XbarZ V H)} (hA₀ : A₀ ∈ Δ) (hVA : VZ V H ≤ A₀) : VZ V H = A₀ := by
  have hgenF := hG (XbarZ V H) Δ hΔ h4 A₀ hA₀
  have htorF := hTor (XbarZ V H) Δ hΔ h4 A₀ hA₀
  have hE1 : VZ V H ≠ ⊥ := hc.Vtilde_ne_bot hd
  by_contra hne
  obtain ⟨nh, hnhN, hnhne⟩ : ∃ nh ∈ Subgroup.normalizer (A₀ : Set (XbarZ V H)),
      conjSub (VZ V H) nh ≠ VZ V H := by
    by_contra hall
    push Not at hall
    have h1 := htorF (VZ V H) hVA hE1
    have h2 : (⨆ n ∈ Subgroup.normalizer (A₀ : Set (XbarZ V H)), conjSub (VZ V H) n) =
        VZ V H := by
      refine le_antisymm (iSup₂_le fun n hn => (hall n hn).le) ?_
      refine le_iSup₂_of_le (1 : XbarZ V H) (Subgroup.one_mem _) ?_
      rw [conjSub_one]
    exact hne (h2.symm.trans h1)
  have hnhA : conjSub (VZ V H) nh ≤ A₀ := by
    have hA : conjSub A₀ nh = A₀ := mem_normalizer_iff_conjSubgroup_eq.mp hnhN
    rw [← hA]
    exact Subgroup.map_mono hVA
  set 𝒩 : Set (XbarZ V H) :=
    {n | conjSub (VZ V H) n ≤ Subgroup.centralizer (A₀ : Set (XbarZ V H))} with h𝒩
  have hV : ∀ n ∈ 𝒩, ∀ a ∈ conjSubgroup n (VZ V H), ∀ b ∈ VZ V H, a * b = b * a := by
    intro n hn a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hn ha) b (hVA hb)).symm
  have hVh : ∀ n ∈ 𝒩, ∀ a ∈ conjSubgroup n (VZ V H), ∀ b ∈ conjSubgroup nh (VZ V H),
      a * b = b * a := by
    intro n hn a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hn ha) b (hnhA hb)).symm
  obtain ⟨B, hB, hopp⟩ := hΔ.cls.noIsolated hΔ.points hΔ.rank A₀ hA₀
  obtain ⟨w, hw⟩ := hΔ.cls.root.exists_conjSub_eq hA₀ hB
  obtain ⟨⟨v, hvE⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have ha₀E : w * v * w⁻¹ ∈ conjSubgroup w (VZ V H) := by
    rw [mem_conjSubgroup, show w⁻¹ * (w * v * w⁻¹) * w = v by group]
    exact hvE
  have ha₀B : w * v * w⁻¹ ∈ B := by
    rw [← hw]
    exact Subgroup.map_mono hVA ha₀E
  have ha₀1 : w * v * w⁻¹ ≠ 1 := by
    intro h
    apply hv1'
    have h2 : w⁻¹ * (w * v * w⁻¹) * w = 1 := by rw [h]; group
    rwa [show w⁻¹ * (w * v * w⁻¹) * w = v by group] at h2
  have hgen0 := hgenF B hB hopp (w * v * w⁻¹) ha₀B ha₀1
  refine hc.false_of_cover hd 𝒩 hnhne hV hVh ha₀E ha₀1 ?_
  refine eq_top_iff.mpr ?_
  rw [← hgen0]
  refine sup_le_sup_right (iSup₂_le fun C hC => iSup_le fun hCc => ?_) _
  obtain ⟨y, hy⟩ := hΔ.cls.root.exists_conjSub_eq hA₀ hC
  have htor := htorF (VZ V H) hVA hE1
  rw [← hy, ← htor]
  rw [← hy] at hCc
  have : conjSub (⨆ n ∈ Subgroup.normalizer (A₀ : Set (XbarZ V H)), conjSub (VZ V H) n) y =
      ⨆ n ∈ Subgroup.normalizer (A₀ : Set (XbarZ V H)), conjSub (VZ V H) (y * n) := by
    unfold conjSub
    simp only [Subgroup.map_iSup]
    refine iSup_congr fun n => iSup_congr fun _ => ?_
    exact (conjSub_mul (VZ V H) y n).symm
  rw [this]
  refine iSup₂_le fun n hn => ?_
  refine le_iSup₂_of_le (y * n) ?_ le_rfl
  show conjSub (VZ V H) (y * n) ≤ Subgroup.centralizer (A₀ : Set (XbarZ V H))
  refine le_trans ?_ hCc
  rw [conjSub_mul]
  exact Subgroup.map_mono (by
    have hnA : conjSub A₀ n = A₀ := mem_normalizer_iff_conjSubgroup_eq.mp hn
    rw [← hnA]
    exact Subgroup.map_mono hVA)

end MinCex

open CFSG.Timmesfeld (rootSet)

theorem tim79aIdentConnectedStatement_of_inputs (hL2 : CFSG.RankThree.GF2n.Tim81.OddTranspRootL2)
    (hT : TransvectionStatement) (hG : TransvectionGenerationStatement)
    (hTor : TransvectionTorusStatement) :
    Tim79aIdentConnectedStatement := by
  intro G _ _ M V Q P H hs hms hconn
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hd : Sec23Data V H := hs.data
  have hsimple : IsSimpleGroup (XbarZ V H) := hc.tilde_isSimple hd hs.degenerate hms
  have hsetup := hc.tilde_setup hd hs.degenerate
  have hnab : ∃ a b : XbarZ V H, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    obtain ⟨u, hu, v, hv, huv, -, -⟩ := hms
    obtain ⟨d₀, hd₀⟩ := hsetup.isClass
    rw [hd₀] at hu hv
    obtain ⟨c, hc'⟩ := isConj_iff.mp hu
    obtain ⟨c', hc''⟩ := isConj_iff.mp hv
    apply huv
    rw [← hc', ← hc'', hab c d₀, hab c' d₀]
    simp
  have hnab' : ¬ IsMulCommutative (XbarZ V H) := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (h.is_comm.comm a b)
  have hZ : Subgroup.center (XbarZ V H) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnab'
  have hP : pCore 2 (XbarZ V H) = ⊥ := CFSG.CGT.PushingUp.pCore_eq_bot_of_isSimpleGroup hnab
  have hΔ := transvectionHyp_of_connected hL2 hsetup hP hZ hms hconn
  set Δ : Set (Subgroup (XbarZ V H)) :=
    {A | ∃ d ∈ Dtilde V H, A = Subgroup.closure (rootSet (Dtilde V H) d)} with hΔdef
  obtain ⟨f, hf, hcard, hconcl⟩ := hT (XbarZ V H) Δ hΔ
  have h4 : ∀ A ∈ Δ, 4 ≤ Nat.card A := by
    rintro A ⟨d, hdD, rfl⟩
    exact four_le_card_closure_rootSet hsetup hms d hdD
  obtain ⟨v₀, hv₀V, hv₀1, hv₀D⟩ := hc.exists_Vtilde_ne_one hd
  set A₀ : Subgroup (XbarZ V H) := Subgroup.closure (rootSet (Dtilde V H) v₀) with hA₀def
  have hA₀ : A₀ ∈ Δ := ⟨v₀, hv₀D, rfl⟩
  have hVA : VZ V H ≤ A₀ := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact A₀.one_mem
    by_cases hvv : v = v₀
    · rw [hvv]
      exact Subgroup.subset_closure ⟨hv₀D, fun f _ => Iff.rfl⟩
    have hvD : v ∈ Dtilde V H := hc.Vtilde_mem_Dtilde hv hv1
    have hcomm : Commute v₀ v := (hc.isElemAbelian_Vtilde.1.is_comm.comm ⟨v₀, hv₀V⟩ ⟨v, hv⟩ |>
      congrArg Subtype.val)
    have hw1 : v₀ * v ≠ 1 := by
      intro h
      apply hvv
      have : v = v₀⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      have hsq : v₀ * v₀ = 1 := by
        have h0 := pow_orderOf_eq_one v₀
        rwa [hsetup.oddT.1 v₀ hv₀D, pow_two] at h0
      exact inv_eq_of_mul_eq_one_right hsq
    have hwV : v₀ * v ∈ VZ V H := (VZ V H).mul_mem hv₀V hv
    have hwD : v₀ * v ∈ Dtilde V H := hc.Vtilde_mem_Dtilde hwV hw1
    exact Subgroup.subset_closure (mem_rootSet_of_mul_mem hsetup.oddT hv₀D hvD hcomm hwD)
  have hVEq : VZ V H = A₀ := hc.vtilde_eq_of_le hd hG hTor hΔ h4 hA₀ hVA
  have hcls : rootClassZ V H = Δ := by
    ext A
    constructor
    · rintro ⟨x, rfl⟩
      rw [hVEq, hA₀def, conjSub_closure_rootSet hsetup v₀ x hv₀D]
      refine ⟨x * v₀ * x⁻¹, ?_, rfl⟩
      obtain ⟨d₀, hd₀⟩ := hsetup.isClass
      have h1 : IsConj d₀ v₀ := by
        have h0 := hv₀D
        rw [hd₀] at h0
        exact h0
      have h2 : IsConj v₀ (x * v₀ * x⁻¹) := isConj_iff.mpr ⟨x, rfl⟩
      rw [hd₀]
      exact h1.trans h2
    · rintro ⟨d, hdD, rfl⟩
      obtain ⟨d₀, hd₀⟩ := hsetup.isClass
      have hdc : IsConj v₀ d := by
        have h1 : IsConj d₀ v₀ := by rw [hd₀] at hv₀D; exact hv₀D
        have h2 : IsConj d₀ d := by rw [hd₀] at hdD; exact hdD
        exact h1.symm.trans h2
      obtain ⟨x, hx⟩ := isConj_iff.mp hdc
      refine ⟨x, ?_⟩
      rw [hVEq, hA₀def, conjSub_closure_rootSet hsetup v₀ x hv₀D, hx]
  have hqB : qBar V H = 2 ^ f := by
    have h1 : Nat.card (VZ V H) = Nat.card (barOf V H V) := hc.card_Vtilde hd
    rw [qBar, ← h1, hVEq]
    exact (hcard A₀ hA₀)
  refine ⟨?_, ?_⟩
  · rw [transvectionConclusion_iff] at hconcl
    rcases hconcl with hsp | hsu
    · left
      exact ⟨f, hf, hqB.symm, by rw [hcls]; exact hsp⟩
    · right
      exact ⟨f, hf, hqB.symm, by rw [hcls]; exact hsu⟩
  · rw [hqB]
    have := h4 A₀ hA₀
    rw [← hcard A₀ hA₀]
    exact this

end CFSG.RankThree.GF2n.Tim79a
