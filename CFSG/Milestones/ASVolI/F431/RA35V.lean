module

public import CFSG.Milestones.ASVolI.F431.Final
public import CFSG.Milestones.ASVolI.F431.J3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section V

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4r_conj_M2_of_V (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hκ : κ = .U4 ∨ κ = .U5)
    (hGp : Gp = ⊤) {V : Subgroup E} (hVeq : V = ctr (pCoreOf 2 (Gp ⊓ M₂)))
    (hVS : V ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVsq : ∀ a ∈ V, a * a = 1)
    (hVu : ∀ A : Subgroup E, A ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a * a = 1) →
        Nat.card A = Nat.card V → A = V)
    {w v : ↥(M₁ ⊓ M₂)} (hwV : (w : E) ∈ V) (hvV : (v : E) ∈ V)
    (h : IsConj (bM β ε w) (bM β ε v)) :
    ∃ m ∈ M₂, m * (w : E) * m⁻¹ = (v : E) := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set b1 := burnsideF4d_bOne β ε with hb1def
  set b2 := burnsideF4d_bTwo β ε with hb2def
  have hb1 : Function.Injective b1 := burnsideF4j_bOne_injective hyp
  have hb2 : Function.Injective b2 := burnsideF4j_bTwo_injective hyp
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hS1 : S ≤ M₁ := fun s hs => (hSB hs).2.1
  have hS12 : S ≤ M₁ ⊓ M₂ := fun s hs => (hSB hs).2
  have hV1 : V ≤ M₁ := hVS.trans hS1
  have hV2 : V ≤ M₂ := fun a ha => (hS12 (hVS ha)).2
  obtain ⟨hSyl, -⟩ := burnsideF4j_sylow_data hyp.amalgam
  have hS_syl : IsSylowTwoOf S (M₁ ⊓ M₂) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right hSyl hS12 (by rw [hGp]; exact le_top)
  set T := subImg b1 S with hTdef
  have hT12 : IsSylowTwoOf T (MiOne β ε ⊓ MiTwo β ε) := by
    rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj]
    exact (burnsideF4j_isSylow_subImg_iff _ hb1 hS1 inf_le_left).2 hS_syl
  have hT : IsSylowTwoOf T ⊤ := burnsideF4m_F_4_33 κ f E Gp M₁ M₂ Y β M ε z hyp T hT12
  have hTidx : ¬ 2 ∣ T.index := by
    have h2 : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  let S' : Sylow 2 M := hT.2.1.toSylow hTidx
  have hS' : (S' : Subgroup M) = T := rfl
  set VM := subImg b1 V with hVMdef
  have hVMT : VM ≤ (S' : Subgroup M) := hS' ▸ subImg_mono b1 hVS
  have hVM12 : VM = subImg b2 V := subImg_eq_of_agree (burnsideF4j_bOne_eq_bTwo β ε) hV1 hV2
  have hVMctr : VM = ctr (pCoreOf 2 (GiTwo Gp β ε)) := by
    rw [hVM12, burnsideF4d_GiTwo_eq, subImg_pCoreOf hb2 inf_le_right,
      burnsideF4j_ctr_subImg _ hb2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right),
      ← hVeq]
  have hN : Subgroup.normalizer (VM : Set M) = MiTwo β ε := by
    rw [hVMctr]
    exact (hyp.ha (Or.inr hκ)).2
  have hVMab : ∀ a ∈ VM, ∀ b ∈ VM, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, hxV, rfl⟩ := mem_subImg.mp ha
    obtain ⟨y, hy, hyV, rfl⟩ := mem_subImg.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hVab x hxV y hyV)
  have hVMcard : Nat.card VM = Nat.card V := by
    rw [hVMdef, subImg, Subgroup.card_map_of_injective hb1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV1).toEquiv
  have hW : IsWeaklyClosedIn VM (S' : Subgroup M) := by
    intro g hg
    rw [hS'] at hg
    set W := conjSubgroup VM g with hWdef
    have hmemW : ∀ x, x ∈ W ↔ g * x * g⁻¹ ∈ VM := fun x => mem_conjSubgroup_iff
    have hWcard : Nat.card W = Nat.card VM := by
      rw [hWdef, conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    set A : Subgroup E := (W.comap b1).map M₁.subtype with hAdef
    have hmemA : ∀ m : ↥M₁, (m : E) ∈ A ↔ b1 m ∈ W := by
      intro m
      constructor
      · rintro ⟨m', hm', he⟩
        have : m' = m := Subtype.ext he
        rw [← this]
        exact hm'
      · intro hm
        exact ⟨m, hm, rfl⟩
    have hAM : A ≤ M₁ := Subgroup.map_subtype_le _
    have hAS : A ≤ S := by
      intro a ha
      obtain ⟨m, hm, rfl⟩ := ha
      obtain ⟨s, hsM, hsS, hse⟩ := mem_subImg.mp (hg hm)
      have : m = ⟨s, hsM⟩ := hb1 hse.symm
      rw [this]
      exact hsS
    have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have haW := (hmemA ⟨a, hAM ha⟩).1 ha
      have hbW := (hmemA ⟨b, hAM hb⟩).1 hb
      have hc := hVMab _ ((hmemW _).1 haW) _ ((hmemW _).1 hbW)
      have hc' : b1 ⟨a, hAM ha⟩ * b1 ⟨b, hAM hb⟩ = b1 ⟨b, hAM hb⟩ * b1 ⟨a, hAM ha⟩ := by
        have e : g * (b1 ⟨a, hAM ha⟩ * b1 ⟨b, hAM hb⟩) * g⁻¹ =
            g * (b1 ⟨b, hAM hb⟩ * b1 ⟨a, hAM ha⟩) * g⁻¹ := by
          calc g * (b1 ⟨a, hAM ha⟩ * b1 ⟨b, hAM hb⟩) * g⁻¹
              = (g * b1 ⟨a, hAM ha⟩ * g⁻¹) * (g * b1 ⟨b, hAM hb⟩ * g⁻¹) := by group
            _ = (g * b1 ⟨b, hAM hb⟩ * g⁻¹) * (g * b1 ⟨a, hAM ha⟩ * g⁻¹) := hc
            _ = g * (b1 ⟨b, hAM hb⟩ * b1 ⟨a, hAM ha⟩) * g⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel e)
      rw [← map_mul, ← map_mul] at hc'
      exact congrArg Subtype.val (hb1 hc')
    have hAsq : ∀ a ∈ A, a * a = 1 := by
      intro a ha
      have haW := (hmemA ⟨a, hAM ha⟩).1 ha
      obtain ⟨x, hx, hxV, hxe⟩ := mem_subImg.mp ((hmemW _).1 haW)
      have h1 : b1 ⟨x, hx⟩ * b1 ⟨x, hx⟩ = 1 := by
        rw [← map_mul]
        have : (⟨x, hx⟩ : ↥M₁) * ⟨x, hx⟩ = 1 := Subtype.ext (hVsq x hxV)
        rw [this, map_one]
      rw [hxe] at h1
      have h2 : b1 ⟨a, hAM ha⟩ * b1 ⟨a, hAM ha⟩ = 1 := by
        have e : g * (b1 ⟨a, hAM ha⟩ * b1 ⟨a, hAM ha⟩) * g⁻¹ = 1 := by
          calc g * (b1 ⟨a, hAM ha⟩ * b1 ⟨a, hAM ha⟩) * g⁻¹
              = (g * b1 ⟨a, hAM ha⟩ * g⁻¹) * (g * b1 ⟨a, hAM ha⟩ * g⁻¹) := by group
            _ = 1 := h1
        have e2 : b1 ⟨a, hAM ha⟩ * b1 ⟨a, hAM ha⟩ =
            g⁻¹ * (g * (b1 ⟨a, hAM ha⟩ * b1 ⟨a, hAM ha⟩) * g⁻¹) * g := by group
        rw [e2, e]
        group
      rw [← map_mul, ← map_one b1] at h2
      exact congrArg Subtype.val (hb1 h2)
    have hWle : W ≤ b1.range := by
      intro y hy
      obtain ⟨s, hsM, -, hse⟩ := mem_subImg.mp (hg hy)
      exact ⟨⟨s, hsM⟩, hse⟩
    have hAcard : Nat.card A = Nat.card V := by
      rw [hAdef, Subgroup.card_map_of_injective M₁.subtype_injective]
      have := Subgroup.card_map_of_injective hb1 (K := W.comap b1)
      rw [Subgroup.map_comap_eq_self hWle] at this
      rw [← this, hWcard, hVMcard]
    have hAV := hVu A hAS hAab hAsq hAcard
    have hWA : W = subImg b1 A := by
      ext y
      constructor
      · intro hy
        obtain ⟨m, hm⟩ := hWle hy
        refine mem_subImg.mpr ⟨m, m.2, (hmemA m).2 (hm ▸ hy), hm⟩
      · intro hy
        obtain ⟨x, hx, hxA, rfl⟩ := mem_subImg.mp hy
        exact (hmemA ⟨x, hx⟩).1 hxA
    rw [hWA, hAV]
  have hwVM : bM β ε w ∈ VM := by
    rw [burnsideF4j_bM_eq_bOne]
    exact mem_subImg_of_mem b1 w.2.1 hwV
  have hvVM : bM β ε v ∈ VM := by
    rw [burnsideF4j_bM_eq_bOne]
    exact mem_subImg_of_mem b1 v.2.1 hvV
  have hcen : ∀ {y : M}, y ∈ VM → y ∈ Subgroup.centralizer (VM : Set M) := fun hy =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hVMab a ha _ hy
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨n, hn, hnv⟩ := burnside_fusion_lemma_centralizer S' hVMT hW (hcen hwVM) (hcen hvVM)
    (g := c⁻¹) (by rw [inv_inv]; exact hc)
  have hnM : n ∈ MiTwo β ε := hN ▸ hn
  rw [burnsideF4d_MiTwo_eq, subImg_self] at hnM
  obtain ⟨m, rfl⟩ := hnM
  refine ⟨((m⁻¹ : ↥M₂) : E), (m⁻¹).2, ?_⟩
  have hw2 : bM β ε w = b2 ⟨w, w.2.2⟩ := by
    rw [burnsideF4j_bM_eq_bOne]
    exact burnsideF4j_bOne_eq_bTwo β ε w w.2.1 w.2.2
  have hv2 : bM β ε v = b2 ⟨v, v.2.2⟩ := by
    rw [burnsideF4j_bM_eq_bOne]
    exact burnsideF4j_bOne_eq_bTwo β ε v v.2.1 v.2.2
  rw [hw2, hv2, ← map_inv, ← map_mul, ← map_mul] at hnv
  have := congrArg Subtype.val (hb2 hnv)
  simpa [mul_assoc] using this

end V

end CFSG.ASVolI
