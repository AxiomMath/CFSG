module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCentrality

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization commutatorElement

section PartnerCore

variable {G : Type*} [Group G]

structure PartnerCore (S Fp Zp : Subgroup G) : Prop where
  normal : ∀ s ∈ S, ∀ x ∈ Fp, s * x * s⁻¹ ∈ Fp
  zcentral : ∀ s ∈ S, ∀ z ∈ Zp, s * z = z * s
  commJ : ⁅thompsonJ S, Fp⁆ = Zp
  commA : ∀ A, IsMaxElemAbelian S A → ⁅A, Fp⁆ = ⊥ ∨ ⁅A, Fp⁆ = Zp
  sup_max : ∀ A, IsMaxElemAbelian S A →
    IsMaxElemAbelian S (Fp ⊔ (A ⊓ Subgroup.centralizer (Fp : Set G)))

namespace PartnerCore

variable {S Fp Zp : Subgroup G}

theorem fp_le [Finite G] (hp : PartnerCore S Fp Zp) : Fp ≤ S := by
  obtain ⟨A, hA⟩ := exists_maxElem S
  exact le_sup_left.trans (hp.sup_max A hA).1

theorem adm [Finite G] (hp : PartnerCore S Fp Zp) : Adm S Fp := by
  obtain ⟨A, hA⟩ := exists_maxElem S
  exact ⟨_, hp.sup_max A hA, le_sup_left⟩

theorem isElemAbelian_fp [Finite G] (hp : PartnerCore S Fp Zp) :
    CFSG.Open.IsElemAbelian 2 Fp :=
  hp.adm.isElemAbelian

theorem zp_le_fp [Finite G] (hp : PartnerCore S Fp Zp) : Zp ≤ Fp := by
  rw [← hp.commJ, Subgroup.commutator_le]
  intro j hj f hf
  have h1 := hp.normal j (thompsonJ_le_self' S hj) f hf
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hf)

theorem zp_le [Finite G] (hp : PartnerCore S Fp Zp) : Zp ≤ S :=
  hp.zp_le_fp.trans hp.fp_le

theorem zp_le_thompsonJ [Finite G] (hp : PartnerCore S Fp Zp) : Zp ≤ thompsonJ S := by
  rw [← hp.commJ, Subgroup.commutator_le]
  intro j hj f hf
  have h1 := thompsonJ_conj_mem_sylow (hp.fp_le hf) (inv_mem hj)
  rw [commutatorElement_def]
  have : j * f * j⁻¹ * f⁻¹ = j * (f * j⁻¹ * f⁻¹) := by group
  rw [this]
  exact mul_mem hj h1

theorem isElemAbelian_zp [Finite G] (hp : PartnerCore S Fp Zp) :
    CFSG.Open.IsElemAbelian 2 Zp :=
  isElemAbelian_mono hp.isElemAbelian_fp hp.zp_le_fp

theorem commA_le [Finite G] (hp : PartnerCore S Fp Zp) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) : ⁅A, Fp⁆ ≤ Zp := by
  rcases hp.commA A hA with h | h
  · rw [h]; exact bot_le
  · exact h.le

theorem sup_max_cj [Finite G] (hp : PartnerCore S Fp Zp) (g : G) {A' : Subgroup G}
    (hA' : IsMaxElemAbelian (cj S g) A') :
    IsMaxElemAbelian (cj S g)
      (cj Fp g ⊔ (A' ⊓ Subgroup.centralizer ((cj Fp g : Subgroup G) : Set G))) := by
  have hA : IsMaxElemAbelian S (cj A' g⁻¹) := by
    have := isMaxElemAbelian_cj g⁻¹ hA'
    rwa [cj_inv_cj] at this
  have h1 := isMaxElemAbelian_cj g (hp.sup_max _ hA)
  rw [cj_sup, cj_inf, ← centralizer_cj, cj_cj_inv] at h1
  exact h1

theorem commA_cj [Finite G] (hp : PartnerCore S Fp Zp) (g : G) {A' : Subgroup G}
    (hA' : IsMaxElemAbelian (cj S g) A') :
    ⁅A', cj Fp g⁆ = ⊥ ∨ ⁅A', cj Fp g⁆ = cj Zp g := by
  have hA : IsMaxElemAbelian S (cj A' g⁻¹) := by
    have := isMaxElemAbelian_cj g⁻¹ hA'
    rwa [cj_inv_cj] at this
  have h2 : cj ⁅cj A' g⁻¹, Fp⁆ g = ⁅A', cj Fp g⁆ := by
    rw [cj_commutator, cj_cj_inv]
  rcases hp.commA _ hA with h1 | h1
  · left; rw [← h2, h1, cj_bot]
  · right; rw [← h2, h1]

end PartnerCore

@[expose] def BoneP (Fp A : Subgroup G) : Subgroup G :=
  Fp ⊔ (Bzero A ⊓ Subgroup.centralizer (Fp : Set G))

@[expose] def CtrP (Fp A : Subgroup G) (g : G) : Subgroup G :=
  BoneP Fp A ⊓ Subgroup.centralizer ((cj Fp g : Subgroup G) : Set G)

end PartnerCore

section Chain

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Fp Zp : Subgroup G}

namespace PartnerCore

omit [Finite G] in
theorem Zfix_sup_le_centralizer (hp : PartnerCore (S : Subgroup G) Fp Zp) :
    Zfix S ⊔ Zp ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
  sup_le (fun _ hz => Subgroup.mem_centralizer_iff.mpr fun _ hs => IsSeed.Zfix_central hz hs)
    (fun _ hz => Subgroup.mem_centralizer_iff.mpr fun _ hs => hp.zcentral _ hs _ hz)

theorem zp_le_Fcore (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCore (S : Subgroup G) Fp Zp) :
    Zp ≤ Fcore G := fun z hz =>
  h.mem_Fcore_of_central_involution (hp.zp_le hz) (fun t ht => (hp.zcentral t ht z hz).symm)
    ((isElemAbelian_iff.mp hp.isElemAbelian_zp).2 z hz)

theorem Zfix_sup_zp_le_Fcore (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) : Zfix S ⊔ Zp ≤ Fcore G :=
  sup_le h.Zfix_le_Fcore (zp_le_Fcore h hp)

theorem fp_le_thompsonJ_core (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) :
    Fp ≤ thompsonJ (CFSG.pCore 2 G) := by
  obtain ⟨A, hA, hle⟩ := h.adm_core_of_adm hp.adm hFQ
  exact hle.trans (maxElem_le_thompsonJ hA)

theorem BoneP_isMax (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCore (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    IsMaxElemAbelian (S : Subgroup G) (BoneP Fp A) ∧ BoneP Fp A ≤ CFSG.pCore 2 G ∧
      IsMaxElemAbelian (CFSG.pCore 2 G) (BoneP Fp A) := by
  have hS : IsMaxElemAbelian (S : Subgroup G) (BoneP Fp A) :=
    hp.sup_max _ (h.Bzero_isMax hA).2
  have hQ : BoneP Fp A ≤ CFSG.pCore 2 G :=
    sup_le hFQ (inf_le_left.trans (h.Bzero_isMax hA).1.1)
  exact ⟨hS, hQ, IsSeed.isMaxElemAbelian_core_of_le hS hQ⟩

theorem BoneP_normalized (hp : PartnerCore (S : Subgroup G) Fp Zp) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) {a : G} (ha : a ∈ A) {b : G}
    (hb : b ∈ BoneP Fp A) : a * b * a⁻¹ ∈ BoneP Fp A := by
  have : BoneP Fp A ≤ cj (BoneP Fp A) a := by
    refine sup_le (fun x hx => mem_cj.mpr ?_) (fun x hx => mem_cj.mpr ?_)
    · exact Subgroup.mem_sup_left (hp.normal a (hA.1 ha) x hx)
    · obtain ⟨hxB0, hxc⟩ := hx
      apply Subgroup.mem_sup_right
      refine ⟨IsSeed.Bzero_normalized hA ha hxB0, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : a⁻¹ * w * a⁻¹⁻¹ ∈ Fp := hp.normal a⁻¹ ((S : Subgroup G).inv_mem (hA.1 ha)) w hw
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ hw'
      calc w * (a * x * a⁻¹) = a * ((a⁻¹ * w * a⁻¹⁻¹) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * w * a⁻¹⁻¹)) * a⁻¹ := by rw [hcomm]
        _ = a * x * a⁻¹ * w := by group
  exact mem_cj.mp (this hb)

theorem commutator_A_BoneP_le (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    ⁅A, BoneP Fp A⁆ ≤ Zfix S ⊔ Zp := by
  have hZZ := Zfix_sup_le_centralizer hp
  have hNV : ∀ n ∈ (S : Subgroup G), ∀ v ∈ Zfix S ⊔ Zp, n * v * n⁻¹ ∈ Zfix S ⊔ Zp :=
    fun n hn v hv => mem_of_central_conj hZZ hn hv
  have hNV' : ∀ n ∈ (S : Subgroup G), ∀ v ∈ Zfix S, n * v * n⁻¹ ∈ Zfix S := fun n hn v hv =>
    mem_of_central_conj (fun z hz => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      IsSeed.Zfix_central hz hs) hn hv
  have hB0 : ⁅A, Bzero A⁆ ≤ Zfix S := by
    refine commutator_sup_le hNV' (inf_le_left.trans hA.1) (Fcore_le_sylow (S := S)) ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha x hx
      have hc : a * x = x * a := (isElemAbelian_iff.mp hA.2.1).1 a ha x hx.1
      have : ⁅a, x⁆ = 1 := by
        simp only [commutatorElement_def]; rw [hc]; group
      rw [this]; exact one_mem _
    · rw [h.commutator_A_Fcore hA hAQ]
  refine commutator_sup_le hNV hp.fp_le (inf_le_left.trans (h.Bzero_isMax hA).2.1) ?_ ?_
  · exact (hp.commA_le hA).trans le_sup_right
  · exact ((Subgroup.commutator_mono le_rfl inf_le_left).trans hB0).trans le_sup_left

omit [Finite G] in
theorem cj_fp_le_core (hFQ : Fp ≤ CFSG.pCore 2 G) (g : G) : cj Fp g ≤ CFSG.pCore 2 G := by
  have h1 := cj_mono (g := g) hFQ
  rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h1
  exact h1

theorem cj_fp_le_thompsonJ_core (hFJ : Fp ≤ thompsonJ (CFSG.pCore 2 G)) (g : G) :
    cj Fp g ≤ thompsonJ (CFSG.pCore 2 G) := by
  have h1 := cj_mono (g := g) hFJ
  rw [cj_eq_self_of_normal (Y := thompsonJ (CFSG.pCore 2 G))] at h1
  exact h1

theorem Fcore_commute_cj (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCore (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) (g : G) {f w : G} (hf : f ∈ Fcore G) (hw : w ∈ cj Fp g) :
    f * w = w * f :=
  (Fcore_commute_thompsonJ_core hf
    (cj_fp_le_thompsonJ_core (fp_le_thompsonJ_core h hp hFQ) g hw)).symm

theorem cj_mem_of_mem_thompsonJ_core (hp : PartnerCore (S : Subgroup G) Fp Zp) (g : G) {a : G}
    (ha : a ∈ thompsonJ (CFSG.pCore 2 G)) {x : G} (hx : x ∈ cj Fp g) : a * x * a⁻¹ ∈ cj Fp g := by
  rw [mem_cj] at hx ⊢
  have hga : g * a * g⁻¹ ∈ thompsonJ (CFSG.pCore 2 G) := thompsonJ_conj_mem ha g
  have := hp.normal _ (core_le_sylow S (thompsonJ_le_self' _ hga)) _ hx
  have e : g * (a * x * a⁻¹) * g⁻¹ = (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
  rw [e]
  exact this

theorem commutator_A_BoneP_le_C (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) (g : G) :
    ⁅A, BoneP Fp A⁆ ≤ CtrP Fp A g := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ (⁅A, BoneP Fp A⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ha hb
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  · have h1 : a * b * a⁻¹ ∈ BoneP Fp A := BoneP_normalized hp hA ha hb
    have : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact mul_mem h1 ((BoneP Fp A).inv_mem hb)
  · have hF : ⁅a, b⁆ ∈ Fcore G :=
      Zfix_sup_zp_le_Fcore h hp (commutator_A_BoneP_le h hp hA hAQ hmem)
    exact (Fcore_commute_cj h hp hFQ g hF hw).symm

theorem cj_CtrP_eq (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCore (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) (g : G) {a : G}
    (ha : a ∈ A) : cj (CtrP Fp A g) a = CtrP Fp A g := by
  apply cj_eq_of_forall_mem
  intro x hx
  have hcomm : ⁅a, x⁆ ∈ CtrP Fp A g :=
    commutator_A_BoneP_le_C h hp hFQ hA hAQ g (Subgroup.commutator_mem_commutator ha hx.1)
  have : a * x * a⁻¹ = ⁅a, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem hcomm hx

theorem CtrP_le_centralizer_cj (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) (g : G) {a : G}
    (ha : a ∈ A) :
    CtrP Fp A g ≤ Subgroup.centralizer ((cj (cj Fp g) a : Subgroup G) : Set G) := by
  have h1 : CtrP Fp A g ≤ Subgroup.centralizer ((cj Fp g : Subgroup G) : Set G) := inf_le_right
  have h2 := cj_mono (g := a) h1
  rw [cj_CtrP_eq h hp hFQ hA hAQ g ha, ← centralizer_cj] at h2
  exact h2

theorem CtrP_sup_isMax (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCore (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A)
    (g : G) : IsMaxElemAbelian (CFSG.pCore 2 G) (cj Fp g ⊔ CtrP Fp A g) := by
  obtain ⟨hBS, hBQ, hBQmax⟩ := BoneP_isMax h hp hFQ hA
  have h1 := hp.sup_max_cj g (A' := BoneP Fp A) (h.isMaxElemAbelian_cj_of_core hBQmax g)
  have hQ : cj Fp g ⊔ CtrP Fp A g ≤ CFSG.pCore 2 G :=
    sup_le (cj_fp_le_core hFQ g) (inf_le_left.trans hBQ)
  exact isMaxElemAbelian_core_of_le_cj (core_le_sylow S) h1 hQ

theorem cj_zp_eq_of_commutator_ne_bot (hp : PartnerCore (S : Subgroup G) Fp Zp) (g x : G)
    {C : Subgroup G}
    (hA₁ : IsMaxElemAbelian (cj (S : Subgroup G) g) (cj (cj Fp g) x ⊔ C))
    (hA₂ : IsMaxElemAbelian (cj (S : Subgroup G) (g * x)) (cj Fp g ⊔ C))
    (hCX : ∀ c ∈ C, ∀ w ∈ cj Fp g, c * w = w * c)
    (hCX' : ∀ c ∈ C, ∀ w ∈ cj (cj Fp g) x, c * w = w * c)
    (hne : ⁅cj Fp g, cj (cj Fp g) x⁆ ≠ ⊥) :
    cj Zp g = cj Zp (g * x) := by
  have hX' : cj (cj Fp g) x = cj Fp (g * x) := cj_cj
  have h1 : ⁅cj (cj Fp g) x ⊔ C, cj Fp g⁆ = ⁅cj (cj Fp g) x, cj Fp g⁆ := by
    apply le_antisymm
    · exact commutator_sup_of_commute (fun p hp c hc => (hCX' c hc p hp).symm) hCX
    · exact Subgroup.commutator_mono le_sup_left le_rfl
  have hne1 : ⁅cj (cj Fp g) x ⊔ C, cj Fp g⁆ ≠ ⊥ := by
    rw [h1, Subgroup.commutator_comm]; exact hne
  have e1 : ⁅cj (cj Fp g) x ⊔ C, cj Fp g⁆ = cj Zp g :=
    (hp.commA_cj g hA₁).resolve_left hne1
  rw [h1, Subgroup.commutator_comm] at e1
  have h2 : ⁅cj Fp g ⊔ C, cj (cj Fp g) x⁆ = ⁅cj Fp g, cj (cj Fp g) x⁆ := by
    apply le_antisymm
    · exact commutator_sup_of_commute (fun p hp c hc => (hCX c hc p hp).symm) hCX'
    · exact Subgroup.commutator_mono le_sup_left le_rfl
  have hne2 : ⁅cj Fp g ⊔ C, cj Fp (g * x)⁆ ≠ ⊥ := by
    rw [← hX', h2]; exact hne
  have e2 : ⁅cj Fp g ⊔ C, cj Fp (g * x)⁆ = cj Zp (g * x) :=
    (hp.commA_cj (g * x) hA₂).resolve_left hne2
  rw [← hX', h2] at e2
  exact e1.symm.trans e2

theorem commutator_cj_eq_bot (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) {g : G}
    (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ)
    {x : G} (hx : x ∈ A) (hxQ : x ∉ CFSG.pCore 2 G) :
    ⁅cj Fp g, cj (cj Fp g) x⁆ = ⊥ := by
  by_contra hne
  have hxS : x ∈ (S : Subgroup G) := hA.1 hx
  have hXC := CtrP_sup_isMax h hp hFQ hA g
  have hCx := cj_CtrP_eq h hp hFQ hA hAQ g hx
  have hA₂ : IsMaxElemAbelian (cj (S : Subgroup G) (g * x)) (cj Fp g ⊔ CtrP Fp A g) :=
    h.isMaxElemAbelian_cj_of_core hXC (g * x)
  have hA₁ : IsMaxElemAbelian (cj (S : Subgroup G) g) (cj (cj Fp g) x ⊔ CtrP Fp A g) := by
    have h1 := isMaxElemAbelian_cj x hXC
    rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G), cj_sup, hCx] at h1
    exact h.isMaxElemAbelian_cj_of_core h1 g
  have hCX : ∀ c ∈ CtrP Fp A g, ∀ w ∈ cj Fp g, c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hCX' : ∀ c ∈ CtrP Fp A g, ∀ w ∈ cj (cj Fp g) x, c * w = w * c := fun c hc w hw =>
    (Subgroup.mem_centralizer_iff.mp (CtrP_le_centralizer_cj h hp hFQ hA hAQ g hx hc) w hw).symm
  have hZ := cj_zp_eq_of_commutator_ne_bot hp g x hA₁ hA₂ hCX hCX' hne
  have hcj : cj (cj Zp g) x = cj Zp g := by
    have : cj (cj Zp g) x = cj Zp (g * x) := cj_cj
    rw [this]
    exact hZ.symm
  have hmem := mem_normalizer_of_cj_cj_eq hcj
  exact hgM (h.mem_Mnorm_of_conj_mem hxS hxQ (hN _ hmem))

theorem cj_fp_le_BoneP (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCore (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A)
    (hAQ : ¬ A ≤ CFSG.pCore 2 G) {g : G} (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ) :
    cj Fp g ≤ BoneP Fp A := by
  obtain ⟨hBS, hBQ, hBQmax⟩ := BoneP_isMax h hp hFQ hA
  have hXQ := cj_fp_le_core hFQ g
  have hXC := CtrP_sup_isMax h hp hFQ hA g
  have hXel : CFSG.Open.IsElemAbelian 2 (cj Fp g) := isElemAbelian_cj hp.isElemAbelian_fp g
  have hCle : CtrP Fp A g ≤ BoneP Fp A := inf_le_left
  have hCX : ∀ c ∈ CtrP Fp A g, ∀ w ∈ cj Fp g, c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hcomm : ∀ a ∈ A, ∀ w ∈ cj Fp g, ∀ y ∈ cj (cj Fp g) a, w * y = y * w := by
    intro a ha w hw y hy
    by_cases haQ : a ∈ CFSG.pCore 2 G
    · have haJ : a ∈ thompsonJ (CFSG.pCore 2 G) :=
        maxElem_le_thompsonJ (h.Bzero_isMax hA).1 (Subgroup.mem_sup_left ⟨ha, haQ⟩)
      have hcjX : cj (cj Fp g) a = cj Fp g :=
        cj_eq_of_forall_mem fun z hz => cj_mem_of_mem_thompsonJ_core hp g haJ hz
      rw [hcjX] at hy
      exact (isElemAbelian_iff.mp hXel).1 w hw y hy
    · exact mul_comm_of_commutator_eq_bot
        (commutator_cj_eq_bot h hp hFQ hA hAQ hgM hN ha haQ) hw hy
  have hXa : ∀ a ∈ A, cj (cj Fp g) a ≤ cj Fp g ⊔ CtrP Fp A g := by
    intro a ha
    refine maxElem_le_of_commute hXC ?_ (isElemAbelian_cj hXel a) ?_
    · have h1 := cj_mono (g := a) hXQ
      rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h1
      exact h1
    · intro y hy u hu
      obtain ⟨w, hw, c, hc, rfl⟩ := mem_sup_of_commute
        (fun x hx c hc => (hCX c hc x hx).symm) hu
      have h1 : w * y = y * w := hcomm a ha w hw y hy
      have h2 : y * c = c * y :=
        Subgroup.mem_centralizer_iff.mp (CtrP_le_centralizer_cj h hp hFQ hA hAQ g ha hc) y hy
      calc y * (w * c) = (y * w) * c := by group
        _ = (w * y) * c := by rw [h1]
        _ = w * (y * c) := by group
        _ = w * (c * y) := by rw [h2]
        _ = w * c * y := by group
  have hNbot : ⁅BoneP Fp A, cj Fp g⁆ = ⊥ := by
    by_contra hne
    have hBg : IsMaxElemAbelian (cj (S : Subgroup G) g) (BoneP Fp A) :=
      h.isMaxElemAbelian_cj_of_core hBQmax g
    have e : ⁅BoneP Fp A, cj Fp g⁆ = cj Zp g := (hp.commA_cj g hBg).resolve_left hne
    have hinv : ∀ a ∈ A, cj ⁅BoneP Fp A, cj Fp g⁆ a = ⁅BoneP Fp A, cj Fp g⁆ := by
      intro a ha
      have h1 : cj ⁅BoneP Fp A, cj Fp g⁆ a = ⁅cj (BoneP Fp A) a, cj (cj Fp g) a⁆ :=
        cj_commutator
      have h2 : cj (BoneP Fp A) a = BoneP Fp A :=
        cj_eq_of_forall_mem fun b hb => BoneP_normalized hp hA ha hb
      have hle : cj ⁅BoneP Fp A, cj Fp g⁆ a ≤ ⁅BoneP Fp A, cj Fp g⁆ := by
        rw [h1, h2]
        calc ⁅BoneP Fp A, cj (cj Fp g) a⁆
            ≤ ⁅BoneP Fp A, cj Fp g ⊔ CtrP Fp A g⁆ :=
              Subgroup.commutator_mono le_rfl (hXa a ha)
          _ = ⁅cj Fp g ⊔ CtrP Fp A g, BoneP Fp A⁆ :=
              Subgroup.commutator_comm _ _
          _ ≤ ⁅cj Fp g, BoneP Fp A⁆ :=
              commutator_sup_of_commute (fun p hp c hc => (hCX c hc p hp).symm)
                (fun c hc b hb => (isElemAbelian_iff.mp hBS.2.1).1 c (hCle hc) b hb)
          _ = ⁅BoneP Fp A, cj Fp g⁆ := Subgroup.commutator_comm _ _
      exact cj_eq_of_le hle
    obtain ⟨a, ha, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    have hcj : cj (cj Zp g) a = cj Zp g := by
      have := hinv a ha
      rw [e] at this
      exact this
    exact hgM (h.mem_Mnorm_of_conj_mem (hA.1 ha) haQ (hN _ (mem_normalizer_of_cj_cj_eq hcj)))
  exact maxElem_le_of_commute hBQmax hXQ hXel fun y hy b hb =>
    (mul_comm_of_commutator_eq_bot hNbot hb hy).symm

theorem exists_core_max_not_commute_partner (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G)
    (hF : ¬ Fp ≤ Fcore G) :
    ∃ A₀ : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) A₀ ∧ ⁅A₀, Fp⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply hF
  intro f hf
  have hfJ : f ∈ thompsonJ (CFSG.pCore 2 G) := fp_le_thompsonJ_core h hp hFQ hf
  refine mem_centerTorsion_iff.mpr ⟨hfJ, fun k hk => ?_,
    (isElemAbelian_iff.mp hp.isElemAbelian_fp).2 f hf⟩
  have hcent : thompsonJ (CFSG.pCore 2 G) ≤ Subgroup.centralizer (({f} : Set G)) := by
    refine thompsonJ_le_of_forall fun A₀ hA₀ a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mul_comm_of_commutator_eq_bot (hall A₀ hA₀) ha hf).symm
  exact (Subgroup.mem_centralizer_iff.mp (hcent hk) f (Set.mem_singleton f)).symm

theorem partner_centrality (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCore (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) (hF : ¬ Fp ≤ Fcore G) :
    Zp ≤ Hone S ⊓ Subgroup.centralizer (Hone S : Set G) := by
  classical
  by_contra hcon
  have hZaT : Zp ≤ thompsonJ (S : Subgroup G) := hp.zp_le_thompsonJ
  have hZaH : Zp ≤ Hone S := hZaT.trans Subgroup.le_normalClosure
  have hnc : ¬ Hone S ≤ Subgroup.centralizer ((Zp : Subgroup G) : Set G) := by
    intro hle
    apply hcon
    exact le_inf hZaH (Subgroup.le_centralizer_iff.mp hle)
  have hZaS : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Zp, s * z = z * s := hp.zcentral
  have hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ :=
    fun y hy => h.normalizer_le_Mnorm hZaS hnc hy
  obtain ⟨g, hgH, hgM⟩ := h.exists_Hone_not_mem_Mnorm
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  have hXB := cj_fp_le_BoneP h hp hFQ hA hAQ hgM hN
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hAX : ⁅A, cj Fp g⁆ ≤ Fcore G :=
    calc ⁅A, cj Fp g⁆ ≤ ⁅A, BoneP Fp A⁆ := Subgroup.commutator_mono le_rfl hXB
      _ ≤ Zfix S ⊔ Zp := commutator_A_BoneP_le h hp hA hAQ
      _ ≤ Fcore G := Zfix_sup_zp_le_Fcore h hp
  have hcjA : ⁅cj A g⁻¹, Fp⁆ ≤ Fcore G := by
    have h1 : ⁅cj A g⁻¹, Fp⁆ = cj ⁅A, cj Fp g⁆ g⁻¹ := by
      rw [cj_commutator, cj_inv_cj]
    rw [h1]
    calc cj ⁅A, cj Fp g⁆ g⁻¹ ≤ cj (Fcore G) g⁻¹ := cj_mono hAX
      _ = Fcore G := cj_eq_self_of_normal
  have hTFa : ⁅thompsonJ (S : Subgroup G), Fp⁆ = Zp := hp.commJ
  have hTnorm : ∀ t ∈ thompsonJ (S : Subgroup G),
      t ∈ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal _ t) fun w hw => ?_
    have h1 : ⁅t, w⁆ ∈ (⁅thompsonJ (S : Subgroup G), Fp⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator ht hw
    rw [hTFa] at h1
    exact zp_le_Fcore h hp h1
  have hAnorm : ∀ y ∈ cj A g⁻¹,
      y ∈ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) := by
    intro y hy
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal _ y) fun w hw => ?_
    exact hcjA (Subgroup.commutator_mem_commutator hy hw)
  have hJsup : Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) ⊔
      CFSG.pCore 2 G = ⊤ := by
    obtain ⟨hmapA, -⟩ := h.max_outside hA hAQ
    have hne : ℓ ≠ ρ g • ℓ := fun e => hgM ((mem_Mnorm_iff hℓ).mpr e.symm)
    refine h.sup_core_eq_top hne ?_ ?_
    · rw [← hℓ, ← hmapA]
      exact Subgroup.map_mono fun a ha => hTnorm a (maxElem_le_thompsonJ hA ha)
    · rw [rootGrp_smul_eq_map, ← hℓ, ← hmapA]
      rintro _ ⟨u, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨g * a * g⁻¹, hAnorm _ ?_, by simp [MulAut.conj_apply, map_mul, map_inv]⟩
      rw [mem_cj]
      simpa [mul_assoc] using ha
  have hH1 : Hone S ≤ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) :=
    Hone_le_of_sup_core_eq_top (fun t ht => hTnorm t ht) hJsup
  have hZaCent : Zp ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun s hs => hp.zcentral s hs z hz
  have hRle : thompsonJ (CFSG.pCore 2 G) ≤ thompsonJ (S : Subgroup G) :=
    h.thompsonJ_core_le_thompsonJ_sylow
  have hupper : ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ ≤ Zp := by
    refine commutator_sup_le (N := (S : Subgroup G))
      (fun n hn v hv => mem_of_central_conj hZaCent hn hv) (Fcore_le_sylow (S := S))
      hp.fp_le ?_ ?_
    · rw [commutator_eq_bot_of_commute fun r hr f hf =>
        (Fcore_commute_thompsonJ_core hf hr)]
      exact bot_le
    · rw [← hTFa]
      exact Subgroup.commutator_mono hRle le_rfl
  have hlower : Zp ≤ ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ := by
    obtain ⟨A₀, hA₀Q, hA₀ne⟩ := exists_core_max_not_commute_partner h hp hFQ hF
    have hA₀S := h.max_core_facts.1 A₀ hA₀Q
    have e : ⁅A₀, Fp⁆ = Zp := (hp.commA A₀ hA₀S).resolve_left hA₀ne
    rw [← e]
    exact Subgroup.commutator_mono (maxElem_le_thompsonJ hA₀Q) le_sup_right
  have hRW : ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ = Zp := le_antisymm hupper hlower
  have hHZ : ∀ y ∈ Hone S, y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G) := by
    intro y hy
    have hyW : cj (Fcore G ⊔ Fp) y = Fcore G ⊔ Fp := by
      apply cj_eq_of_forall_mem
      intro x hx
      exact (Subgroup.mem_normalizer_iff.mp (hH1 hy) x).mp hx
    have h1 : cj ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ y =
        ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ := by
      rw [cj_commutator, cj_eq_self_of_normal (Y := thompsonJ (CFSG.pCore 2 G)), hyW]
    rw [hRW] at h1
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : x ∈ cj Zp y := by rw [h1]; exact hx
      exact mem_cj.mp this
    · intro hx
      have : x ∈ cj Zp y := mem_cj.mpr hx
      rwa [h1] at this
  exact hgM (hN g (hHZ g hgH))

end PartnerCore

end Chain

end CFSG.Quasithin
