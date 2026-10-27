module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ct_rm3_ggInducedSubgroup_mono {G : Type} [Group G] {H H' : Subgroup G}
    (Bs : Subgroup G) (h : H ≤ H') : ggInducedSubgroup H Bs ≤ ggInducedSubgroup H' Bs := by
  rintro φ ⟨g, hg, hgN, hφ⟩
  exact ⟨g, h hg, hgN, hφ⟩

private lemma ct_rm3_ainf_le_inducedSubgroup {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    ggAInf p B Bs x L D J ≤ ggInducedSubgroup ⊤ Bs := by
  simp only [ggAInf]
  refine sup_le ?_ ?_
  · rw [ggAutomizer_eq]
    exact ct_rm3_ggInducedSubgroup_mono Bs le_top
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun _ => ?_
    rw [ggAutomizer_eq]
    exact ct_rm3_ggInducedSubgroup_mono Bs le_top

private lemma ct_rm3_automizer_apply_eq {G : Type} [Group G] {Bs : Subgroup G}
    {H : Subgroup G} {x : G} (hxBs : x ∈ Bs) (hH : H ≤ Subgroup.centralizer ({x} : Set G))
    (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizer H Bs) :
    φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  rw [ggAutomizer] at hφ
  refine Subgroup.closure_induction (p := fun ψ _ => ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, hgH, -, hψ⟩
    apply Subtype.ext
    calc ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by simpa using hψ ⟨x, hxBs⟩
      _ = x := by
        have hgx : g * x = x * g :=
          ((Subgroup.mem_centralizer_iff.mp (hH hgH)) x (Set.mem_singleton x)).symm
        rw [hgx]; group
  · rfl
  · intro ψ χ _ _ hψ hχ
    rw [MulAut.mul_apply, hχ, hψ]
  · intro ψ _ hψ
    calc ψ⁻¹ ⟨x, hxBs⟩ = ψ⁻¹ (ψ ⟨x, hxBs⟩) := by rw [hψ]
      _ = ⟨x, hxBs⟩ := MulAut.inv_apply_self _ _ _

private lemma ct_rm3_eps_zpowers_eq {G : Type} [Group G] [Finite G] {x b : G} {p : ℕ} (hp : p.Prime)
    (hox : orderOf x = p) (hbx : b ∈ Subgroup.zpowers x) (hb1 : b ≠ 1) :
    x ∈ Subgroup.zpowers b := by
  have hdvd : orderOf b ∣ p := by rw [← hox]; exact orderOf_dvd_of_mem_zpowers hbx
  have hordb : orderOf b = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left (fun h => hb1 (orderOf_eq_one_iff.mp h))
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hbx
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hox]
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hordb]
  have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardb])
  exact heq.symm ▸ Subgroup.mem_zpowers x

theorem ggRM_ainf_le_induced {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} : (ggAInf p B Bs x L D J : Set (MulAut ↥Bs)) ⊆ ggInduced ⊤ Bs := by
  intro φ hφ
  exact ct_rm3_ainf_le_inducedSubgroup p B Bs x L D J hφ

theorem ggAutomizer_le_ggAInf_of_nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) :
    ggAutomizer K Bs ≤ ggAInf p B Bs x L D J := by
  rw [ggAInf]
  refine le_sup_of_le_right ?_
  exact (le_iSup (fun _ : GGNbr p B x D J y K => ggAutomizer K Bs) hK).trans
    ((le_iSup (fun K' : Subgroup G =>
        ⨆ (_ : GGNbr p B x D J y K'), ggAutomizer K' Bs) K).trans
      (le_iSup (fun y' => ⨆ K' : Subgroup G,
        ⨆ (_ : GGNbr p B x D J y' K'), ggAutomizer K' Bs) y))

theorem GGNbrSet.automizerJoin_le_ggAInf {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h𝒦 : GGNbrSet p B x D J 𝒦) : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J := by
  rw [ggAutomizerJoin]
  refine sup_le le_sup_left (iSup_le fun K => iSup_le fun hK => ?_)
  obtain ⟨y, hy⟩ := h𝒦.2 K hK
  exact ggAutomizer_le_ggAInf_of_nbr hy

theorem ggRM_AL_fixes_x
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hxBs : x ∈ Bs) :
    ∀ a ∈ ggAutomizer L Bs, a ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  intro a ha
  obtain ⟨-, -, -, hLx, -⟩ := (hcfg.1.1).tableB_facts
  exact ct_rm3_automizer_apply_eq hxBs hLx a ha

theorem ggRM_zero_fixes_x
    (hFix : GGSecFiveFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    (hxBs : x ∈ Bs) (hC : ¬ ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) :
    ∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs_ea, -, -, -⟩ := hconf.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hle : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J := le_sup_left
  push Not at hC
  obtain ⟨b, hb, hb1⟩ := hC
  have hbmem : (b : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J 𝒦 hcfg hsplit b fun φ hφ => hb φ (hle hφ)
  have hbG1 : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hx1 : x ≠ 1 := by
    intro hx
    apply hbG1
    have hbot : Subgroup.zpowers x = ⊥ := by rw [hx, Subgroup.zpowers_one_eq_bot]
    rw [hbot] at hbmem
    simpa using hbmem
  have hxpow : x ^ p = 1 := hBs_ea.2 x hxBs
  have hox : orderOf x = p := orderOf_eq_prime hxpow hx1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ct_rm3_eps_zpowers_eq hp hox hbmem hbG1)
  intro φ hφ
  have hφb : φ b = b := hb φ hφ
  have hbn : b ^ n = (⟨x, hxBs⟩ : ↥Bs) := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hn
  calc φ ⟨x, hxBs⟩ = φ (b ^ n) := by rw [← hbn]
    _ = (φ b) ^ n := map_zpow φ b n
    _ = b ^ n := by rw [hφb]
    _ = ⟨x, hxBs⟩ := hbn

end CFSG.StandardType

end
