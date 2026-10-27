module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBTw
public import CFSG.LocalAnalysis.StandardType.GGFrameTBSUDvdModel
public import CFSG.LocalAnalysis.StandardType.GGFrameTBSUDvdRefl
import CFSG.LocalAnalysis.StandardType.GGFrameModelNum
import CFSG.LocalAnalysis.StandardType.GGFrameModelNumPerm
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag
import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflModel

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly UCoord SpCoord

theorem frameNumIs_frameConn_of_permHom {G : Type} [Group G] {A : Subgroup G} {d : ℕ}
    (hd : 3 ≤ d) {𝒜 : Subgroup (MulAut ↥A)} {Φ : Equiv.Perm (Fin d) →* MulAut ↥A}
    (hinj : Function.Injective Φ) (hrange : Φ.range = 𝒜)
    (hrefl : ∀ σ : Equiv.Perm (Fin d),
      GGIsReflection 3 (Φ σ) ↔ ∃ a b : Fin d, a ≠ b ∧ σ = Equiv.swap a b) :
    FrameNumIs 𝒜 (d * (d - 1) / 2) (some (2 * (d - 2))) ∧ FrameConn 𝒜 := by
  have hS : ∀ u : MulAut ↥A, u ∈ modelReflSet (𝒜 : Set (MulAut ↥A)) ↔
      ∃ a b : Fin d, a ≠ b ∧ u = Φ (Equiv.swap a b) := by
    intro u
    constructor
    · intro hu
      obtain ⟨hS_mem, h2, hfix⟩ := hu
      have hmem : u ∈ Φ.range := by rw [hrange]; exact hS_mem
      obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hmem
      have hreflσ : GGIsReflection 3 (Φ σ) := by
        rw [hσ]
        exact ⟨h2, hfix⟩
      obtain ⟨a, b, hab, hswap⟩ := (hrefl σ).mp hreflσ
      exact ⟨a, b, hab, by rw [← hσ, hswap]⟩
    · rintro ⟨a, b, hab, rfl⟩
      have hmem : Φ (Equiv.swap a b) ∈ 𝒜 := by
        rw [← hrange]
        exact ⟨Equiv.swap a b, rfl⟩
      have hrefl_swap := (hrefl (Equiv.swap a b)).mpr ⟨a, b, hab, rfl⟩
      exact ⟨hmem, hrefl_swap.1, hrefl_swap.2⟩
  have hA_mem : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔
      (MulAut.congr (MulEquiv.refl ↥A)).symm φ ∈ (𝒜 : Set (MulAut ↥A)) := by
    intro φ
    have h_eq : (MulAut.congr (MulEquiv.refl ↥A)).symm φ = φ := by
      ext x
      rfl
    rw [h_eq]
    rfl
  obtain ⟨hN, hC⟩ := modelNumIs_modelConn_of_perm hd Φ hinj hS
  exact frameNumIs_frameConn_of_model (MulEquiv.refl ↥A) hA_mem hN hC

theorem reflGen_of_permHom {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {d : ℕ}
    {Φ : Equiv.Perm (Fin d) →* MulAut ↥A}
    (hrange : Φ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hW : ∀ σ : Equiv.Perm (Fin d), ∃ (w : L')
      (hw : MulAut.conj w ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt 3 A w ∧ Φ σ = ggConjAut A hw)
    (hrefl : ∀ a b : Fin d, a ≠ b → GGIsReflection 3 (Φ (Equiv.swap a b))) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      Subgroup.closure (ggTorusReflSet 3 A) := by
  rw [← hrange]
  rw [MonoidHom.range_eq_map]
  rw [← Equiv.Perm.closure_isSwap]
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨w, hw, hWeyl, hΦ_eq⟩ := hW (Equiv.swap a b)
  refine ⟨w, hw, hWeyl, hΦ_eq, ?_⟩
  simpa [hΦ_eq] using hrefl a b hab

private lemma frameSUD_inducedSub_subset_I {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hψ : Function.Surjective ψ)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
  rintro x ⟨a, ha, hxa⟩
  obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
  exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφaI

private lemma frameSUD_X_is_elem_abelian {R : Type} [Group R]
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')} {p : ℕ}
    (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A) :
    IsElemAbelian p (TypeA.inducedSub ψ A) :=
  TypeA.isElemAbelian_inducedSub hψ hA

private lemma frameSUD_X_map_q_cyclic {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hO : GGOutdiagCyclic R I)
    (hX : TypeA.inducedSub ψ A ≤ I) :
    IsCyclic ((TypeA.inducedSub ψ A).map
      (QuotientGroup.mk' (MulAut.conj : R →* MulAut R).range)) := by
  obtain ⟨φ₀, hI_sub⟩ := hO
  let N := (MulAut.conj : R →* MulAut R).range
  let q := QuotientGroup.mk' N
  have hX_sub : TypeA.inducedSub ψ A ≤ N ⊔ Subgroup.zpowers φ₀ := by
    intro x hx
    exact hI_sub (hX hx)
  have hmap_sub : (TypeA.inducedSub ψ A).map q ≤ Subgroup.zpowers (q φ₀) := by
    haveI : N.Normal := ggInnNormal R
    have h1 : (N ⊔ Subgroup.zpowers φ₀).map q ≤ Subgroup.zpowers (q φ₀) :=
      map_sup_zpowers_le N φ₀
    exact le_trans (Subgroup.map_mono hX_sub) h1
  exact Subgroup.isCyclic_of_le hmap_sub

private lemma frameSUD_X_map_q_card_le {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hO : GGOutdiagCyclic R I) (hA : IsElemAbelian 3 A)
    (hψ : Function.Surjective ψ)
    (hX : TypeA.inducedSub ψ A ≤ I) :
    Nat.card ((TypeA.inducedSub ψ A).map
      (QuotientGroup.mk' (MulAut.conj : R →* MulAut R).range)) ≤ 3 := by
  let N := (MulAut.conj : R →* MulAut R).range
  let q := QuotientGroup.mk' N
  let X := TypeA.inducedSub ψ A
  have hXA : IsElemAbelian 3 X := TypeA.isElemAbelian_inducedSub hψ hA
  have hcyc : IsCyclic (X.map q) := frameSUD_X_map_q_cyclic hO hX
  have hExp : Monoid.exponent (X.map q) ∣ 3 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    have hx3 : x ^ 3 = 1 := hXA.2 x hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxy]
    rw [← map_pow, hx3, map_one]
  have hcarddvd : Nat.card (X.map q) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact hExp
  exact Nat.le_of_dvd (by norm_num) hcarddvd

private lemma frameSUD_card_X_le {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hO : GGOutdiagCyclic R I) (hA : IsElemAbelian 3 A)
    (hψ : Function.Surjective ψ)
    (hX : TypeA.inducedSub ψ A ≤ I) :
    Nat.card (TypeA.inducedSub ψ A) ≤
      3 * Nat.card ((MulAut.conj : R →* MulAut R).range.subgroupOf (TypeA.inducedSub ψ A)) := by
  let N := (MulAut.conj : R →* MulAut R).range
  let q := QuotientGroup.mk' N
  let X := TypeA.inducedSub ψ A
  have hcard_q : Nat.card (X.map q) ≤ 3 := frameSUD_X_map_q_card_le hO hA hψ hX
  let qX : ↥X →* ↥(X.map q) := (q.comp X.subtype).codRestrict (X.map q) (by
    intro x
    exact Subgroup.mem_map_of_mem q x.2)
  have hker : qX.ker = N.subgroupOf X := by
    ext x
    constructor
    · intro hx
      have hx' : q (x : MulAut R) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff (x : MulAut R)).mp hx'
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : MulAut R)).mpr hx
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup qX.ker
  have h1 : Nat.card (↥X ⧸ qX.ker) = Nat.card ↥(X.map q) := by
    have htop : qX.range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, haX, haq⟩ := Subgroup.mem_map.mp x.2
      exact ⟨⟨a, haX⟩, Subtype.ext haq⟩
    have e := QuotientGroup.quotientKerEquivRange qX
    rw [htop] at e
    exact Nat.card_congr (e.toEquiv.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)))
  rw [h1, hker] at hcard
  calc Nat.card X = Nat.card (X.map q) * Nat.card (N.subgroupOf X) := hcard
    _ ≤ 3 * Nat.card (N.subgroupOf X) := Nat.mul_le_mul_right _ hcard_q

private lemma frameSUD_card_A0 {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    Nat.card ((Subgroup.comap ((TypeA.inducedSub ψ A).subtype.comp
      (TypeA.inducedSubEquiv hψ hker hperf (fun a ha => by
        obtain ⟨φ, _, hφ⟩ := hAI a ha
        exact ⟨φ, hφ⟩)).toMonoidHom) (MulAut.conj : R →* MulAut R).range).map A.subtype) =
      Nat.card ((MulAut.conj : R →* MulAut R).range.subgroupOf (TypeA.inducedSub ψ A)) := by
  let N := (MulAut.conj : R →* MulAut R).range
  let X := TypeA.inducedSub ψ A
  let e := TypeA.inducedSubEquiv hψ hker hperf (fun a ha => by
    obtain ⟨φ, _, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩)
  have hcard_map : Nat.card ((Subgroup.comap (X.subtype.comp e.toMonoidHom) N).map A.subtype) =
      Nat.card (Subgroup.comap (X.subtype.comp e.toMonoidHom) N) := by
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective A)
  rw [hcard_map]
  let f : ↥A →* MulAut R := X.subtype.comp e.toMonoidHom
  have hf_inj : Function.Injective f := by
    intro a b h
    have h1 : e a = e b := Subtype.coe_injective h
    exact e.injective h1
  have hf_range : f.range = X := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
      exact ⟨a, by simp [f, ha]⟩
  apply Nat.card_congr
  have hX_proof : ∀ x : Subgroup.comap f N, f x.1 ∈ X := fun x => by
    rw [← hf_range]
    exact ⟨x.1, rfl⟩
  let g : Subgroup.comap f N → N.subgroupOf X := fun x =>
    ⟨⟨f x.1, hX_proof x⟩, x.2⟩
  refine Equiv.ofBijective (fun x : Subgroup.comap f N =>
    (⟨⟨f x.1, hX_proof x⟩, x.2⟩ : N.subgroupOf X)) ?_
  constructor
  · intro a₁ b₁ h₁
    apply Subtype.ext
    exact hf_inj (Subtype.ext_iff.mp (Subtype.ext_iff.mp h₁))
  · intro x
    have hxX : x.1.1 ∈ X := x.1.2
    have hxN : x.1.1 ∈ N := x.2
    obtain ⟨a, ha⟩ := e.surjective x.1
    have hfa : f a = x.1.1 := by
      change X.subtype (e a) = x.1.1
      rw [ha]
      rfl
    refine ⟨⟨a, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hfa]
      exact hxN
    · apply Subtype.ext
      apply Subtype.ext
      exact hfa

private lemma frameSUD_A0_elem_abelian {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian 3 A)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    IsElemAbelian 3 ((Subgroup.comap ((TypeA.inducedSub ψ A).subtype.comp
      (TypeA.inducedSubEquiv hψ hker hperf (fun a ha => by
        obtain ⟨φ, _, hφ⟩ := hAI a ha
        exact ⟨φ, hφ⟩)).toMonoidHom) (MulAut.conj : R →* MulAut R).range).map A.subtype) := by
  let N := (MulAut.conj : R →* MulAut R).range
  let X := TypeA.inducedSub ψ A
  let e := TypeA.inducedSubEquiv hψ hker hperf (fun a ha => by
    obtain ⟨φ, _, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩)
  have hA0_le_A : (Subgroup.comap (X.subtype.comp e.toMonoidHom) N).map A.subtype ≤ A := by
    rintro _ ⟨b, _, rfl⟩
    exact b.2
  exact CFSG.Open.IsElemAbelian.mono hA hA0_le_A

private lemma frameSUD_A0_inner {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (a : MulAut L')
    (ha : a ∈ (Subgroup.comap ((TypeA.inducedSub ψ A).subtype.comp
      (TypeA.inducedSubEquiv hψ hker hperf (fun a ha => by
        obtain ⟨φ, _, hφ⟩ := hAI a ha
        exact ⟨φ, hφ⟩)).toMonoidHom) (MulAut.conj : R →* MulAut R).range).map A.subtype) :
    ∃ l : L', a = MulAut.conj l := by
  let N := (MulAut.conj : R →* MulAut R).range
  let X := TypeA.inducedSub ψ A
  let hA' : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, _, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  let e := TypeA.inducedSubEquiv hψ hker hperf hA'
  obtain ⟨b, hb_mem, hb_eq⟩ := Subgroup.mem_map.mp ha
  have hfa : X.subtype (e b) ∈ N := hb_mem
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hfa
  obtain ⟨l, rfl⟩ := hψ r
  have h_eq : ∀ x : L', ψ (a x) = ψ (MulAut.conj l x) := by
    intro x
    have h1 := TypeA.inducedSubEquiv_apply hψ hker hperf hA' b x
    have h2 : (e b).1 (ψ x) = ψ (l * x * l⁻¹) := by
      have h3 : (e b).1 = MulAut.conj (ψ l) := hr.symm
      rw [h3, MulAut.conj_apply]
      simp only [map_mul, map_inv]
    have h4 : ψ (b.1 x) = ψ (MulAut.conj l x) := by
      rw [← h1, h2, MulAut.conj_apply]
    change ψ (A.subtype b x) = ψ (MulAut.conj l x) at h4
    rw [hb_eq] at h4
    exact h4
  have h_eq2 : a = MulAut.conj l := TypeA.mulAut_eq_of_forall ψ hker hperf h_eq
  exact ⟨l, h_eq2⟩

theorem exists_noncyclic_three_of_outdiagCyclic {R : Type} [Group R] {I : Set (MulAut R)}
    (hO : GGOutdiagCyclic R I) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h27 : 3 ^ 3 ≤ Nat.card A) :
    ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S := by
  let N := (MulAut.conj : R →* MulAut R).range
  let X := TypeA.inducedSub ψ A
  have hA' : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, _, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  let e := TypeA.inducedSubEquiv hψ hker hperf hA'
  have hX_sub_I : ((X : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I :=
    frameSUD_inducedSub_subset_I hψ hAI
  have hXA : IsElemAbelian 3 X := TypeA.isElemAbelian_inducedSub hψ hA
  have hcardX_le : Nat.card X ≤ 3 * Nat.card (N.subgroupOf X) :=
    frameSUD_card_X_le hO hA hψ hX_sub_I
  let A₀ : Subgroup (MulAut L') := (Subgroup.comap (X.subtype.comp e.toMonoidHom) N).map A.subtype
  have hcardA0 : Nat.card A₀ = Nat.card (N.subgroupOf X) :=
    frameSUD_card_A0 hψ hker hperf hAI
  have hcardA : Nat.card A = Nat.card X :=
    (TypeA.card_inducedSub hψ hker hperf hA').symm
  have hA0_ge : 9 ≤ Nat.card A₀ := by
    rw [hcardA0]
    have h1 : Nat.card A ≤ 3 * Nat.card (N.subgroupOf X) := by
      calc Nat.card A = Nat.card X := hcardA
        _ ≤ 3 * Nat.card (N.subgroupOf X) := hcardX_le
    omega
  have hA0_elem : IsElemAbelian 3 A₀ :=
    frameSUD_A0_elem_abelian hA hψ hker hperf hAI
  have hA0_inner : ∀ a ∈ A₀, ∃ l : L', a = MulAut.conj l := by
    intro a ha
    exact frameSUD_A0_inner hψ hker hperf hAI a ha
  exact exists_noncyclic_three_of_forall_conj hA0_elem hA0_ge hA0_inner



private lemma frameSUD_udPerm_data {m : ℕ} (hm : 8 ≤ m) (h3 : 3 ∣ m + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {r : ℕ} (hrange : (m + 1) / 3 + 2 ≤ r)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ 1))}
    {A : Subgroup (MulAut L')}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hAe : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ 1)))
      (LargeEvenGUSet (Fin (m + 1)) K (2 ^ 1)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ r ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    ∃ (S : Subgroup (Fin (m + 1) → Multiplicative (ZMod 3)))
      (Θ : ↥S →* ↥A) (Φ : Equiv.Perm (Fin (m + 1)) →* MulAut ↥A),
      (S = ⊤ ∨ S = sumZero (m + 1) 3) ∧ Function.Surjective Θ ∧
      (∀ f : ↥S, Θ f = 1 ↔
        ∃ c : Multiplicative (ZMod 3), (f : Fin (m + 1) → Multiplicative (ZMod 3)) = fun _ => c) ∧
      Function.Injective Φ ∧
      Φ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
      (∀ (σ : Equiv.Perm (Fin (m + 1))) (f g : ↥S),
        (g : Fin (m + 1) → Multiplicative (ZMod 3)) =
          permAut σ (f : Fin (m + 1) → Multiplicative (ZMod 3)) →
          Φ σ (Θ f) = Θ g) ∧
      ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ (w : L')
        (hw : MulAut.conj w ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGTorusWeylElt 3 A w ∧ Φ σ = ggConjAut A hw := by
  have hcard : 3 ^ ((m + 1) / 3 + 2) ≤ Nat.card A :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hrange) hr
  have hdn : (m + 1, 1) ≠ (6, 1) := by
    intro h
    have hm6 : m + 1 = 6 := by simpa using congrArg Prod.fst h
    omega
  have hd : 5 ≤ m + 1 := by omega
  exact exists_udPermHom hK le_rfl hdn hd Nat.prime_three (by norm_num)
    h3 hψ hker hperf hAe hAI hcard hsc

theorem frameTBBody_suDvd {m : ℕ} (hm : 8 ≤ m) (h3 : 3 ∣ m + 1) :
    LargeEvenLabelAll ⟨.twA, m, 1⟩ (frameTBBody ⟨.twA, m, 1⟩) := by
  intro Q hQ
  change LargeEvenRecipeUnitary (m + 1) (2 ^ 1) Q at hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  intro r hr6 hrange
  constructor
  · intro L' _ _ ψ A hA
    rcases hA with ⟨hψ, hker, hperf, hAe, hAI, hr, h3A, hsc⟩
    obtain ⟨S, Θ, Φ, hS, hΘ, hk, hinj, hrg, hΦ, hW⟩ :=
      frameSUD_udPerm_data hm h3 hK (hrange.1 rfl) hψ hker hperf hAe hAI hr hsc
    have hrefl := isReflection_quotPerm_iff hS hΘ hk hinj hΦ
    exact reflGen_of_permHom hrg hW fun a b hab => (hrefl _).mpr ⟨a, b, hab, rfl⟩
  · intro L' _ _ ψ A hA
    rcases hA with ⟨hψ, hker, hperf, hAe, hAI, hr, h3A, hsc⟩
    obtain ⟨S, Θ, Φ, hS, hΘ, hk, hinj, hrg, hΦ, hW⟩ :=
      frameSUD_udPerm_data hm h3 hK (hrange.1 rfl) hψ hker hperf hAe hAI hr hsc
    have hrefl := isReflection_quotPerm_iff hS hΘ hk hinj hΦ
    constructor
    · have hres := frameNumIs_frameConn_of_permHom (d := m + 1) (by omega) hinj hrg hrefl
      rw [show frameLabNum ⟨.twA, m, 1⟩ = (m * (m + 1) / 2, some (2 * (m - 1))) by
        simp [frameLabNum, frameTagNum]]
      have h_eq1 : (m + 1) * (m + 1 - 1) / 2 = m * (m + 1) / 2 := by
        rw [Nat.add_sub_cancel, Nat.mul_comm]
      have h_eq2 : 2 * (m + 1 - 2) = 2 * (m - 1) := by omega
      rw [h_eq1, h_eq2] at hres
      exact hres
    · exact exists_noncyclic_three_of_outdiagCyclic (TableB.ggOutdiagCyclic_unitary hK)
        hψ hker hperf hAe hAI (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hr)

end CFSG.StandardType.FrameRoute

end
