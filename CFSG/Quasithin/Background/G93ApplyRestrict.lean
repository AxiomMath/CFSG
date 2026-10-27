module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Range

variable {K K' : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem mem_restrictRange_iff (hK : Invariant K I) {g : GLV ↥I} :
    g ∈ restrictRange K I hK ↔ ∃ k ∈ K, ∀ i : ↥I, ((g i : ↥I) : V) = k (i : V) := by
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, fun i => rfl⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    ext i
    exact (h i).symm

theorem mem_restrictRange_iff' (hK : Invariant K I) {g : GLV ↥I} :
    g ∈ restrictRange K I hK ↔
      ∃ (k : GLV V) (hk : k ∈ K), g = restrictEquiv k I (hK.conjSub_eq hk) := by
  rw [mem_restrictRange_iff hK]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by ext i; exact h i⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, fun i => rfl⟩

theorem restrictRange_congr {K K' : Subgroup (GLV V)} (h : K = K') (hK : Invariant K I)
    (hK' : Invariant K' I) : restrictRange K I hK = restrictRange K' I hK' := by
  subst h
  rfl

theorem conjSub_inv_eq_of_conjSub_eq {a : GLV V} (h : conjSub a I = I) : conjSub a⁻¹ I = I := by
  have := conjSub_inv_conjSub a I
  rwa [h] at this

theorem restrictRange_mono (hK : Invariant K I) (hK' : Invariant K' I) (h : K ≤ K') :
    restrictRange K I hK ≤ restrictRange K' I hK' := by
  intro g hg
  obtain ⟨k, hk, hgk⟩ := (mem_restrictRange_iff hK).1 hg
  exact (mem_restrictRange_iff hK').2 ⟨k, h hk, hgk⟩

theorem restrictRange_sup {L L₂ : Subgroup (GLV V)} (hL : Invariant L I) (hL₂ : Invariant L₂ I)
    (hLL₂ : Invariant (L ⊔ L₂) I) :
    restrictRange (L ⊔ L₂) I hLL₂ = restrictRange L I hL ⊔ restrictRange L₂ I hL₂ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hk, hgk⟩ := (mem_restrictRange_iff hLL₂).1 hg
    set N : Subgroup (GLV ↥I) := restrictRange L I hL ⊔ restrictRange L₂ I hL₂ with hN
    have key : ∀ k ∈ L ⊔ L₂, ∃ hk : conjSub k I = I, restrictEquiv k I hk ∈ N := by
      intro k hk
      rw [Subgroup.sup_eq_closure] at hk
      induction hk using Subgroup.closure_induction with
      | mem k hk =>
        rcases hk with hk | hk
        · exact ⟨hL.conjSub_eq hk, Subgroup.mem_sup_left (restrictEquiv_mem_restrictRange hL hk)⟩
        · exact ⟨hL₂.conjSub_eq hk, Subgroup.mem_sup_right (restrictEquiv_mem_restrictRange hL₂ hk)⟩
      | one =>
        refine ⟨conjSub_one I, ?_⟩
        have : restrictEquiv (1 : GLV V) I (conjSub_one I) = 1 := by
          ext i
          rfl
        rw [this]
        exact N.one_mem
      | mul a b ha hb iha ihb =>
        obtain ⟨ha', ha''⟩ := iha
        obtain ⟨hb', hb''⟩ := ihb
        refine ⟨by rw [conjSub_mul, hb', ha'], ?_⟩
        have : restrictEquiv (a * b) I (by rw [conjSub_mul, hb', ha']) =
            restrictEquiv a I ha' * restrictEquiv b I hb' := by
          ext i
          rfl
        rw [this]
        exact N.mul_mem ha'' hb''
      | inv a ha iha =>
        obtain ⟨ha', ha''⟩ := iha
        refine ⟨conjSub_inv_eq_of_conjSub_eq ha', ?_⟩
        have : restrictEquiv a⁻¹ I (conjSub_inv_eq_of_conjSub_eq ha') =
            (restrictEquiv a I ha')⁻¹ := by
          ext i
          show a⁻¹ (i : V) = ((restrictEquiv a I ha').symm i : V)
          have h1 : a ((restrictEquiv a I ha').symm i : V) = (i : V) := by
            have := (restrictEquiv a I ha').apply_symm_apply i
            exact congrArg Subtype.val this
          conv_lhs => rw [← h1]
          simp
        rw [this]
        exact N.inv_mem ha''
    obtain ⟨hk', hkN⟩ := key k hk
    have : g = restrictEquiv k I hk' := by
      ext i
      exact hgk i
    rw [this]
    exact hkN
  · exact sup_le (restrictRange_mono hL hLL₂ le_sup_left) (restrictRange_mono hL₂ hLL₂ le_sup_right)

end Range

section Faithful

variable {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem faithfulOn_of_le {K K' : Subgroup (GLV V)} (h : K ≤ K') (hf : FaithfulOn K' I) :
    FaithfulOn K I :=
  faithfulOn_iff.2 fun k hk hku => faithfulOn_iff.1 hf k (h hk) hku

theorem restrictHom_injective_of_faithfulOn (hI : Invariant K I) (hf : FaithfulOn K I) :
    Function.Injective (restrictHom K I hI) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [restrictHom_eq_one_iff] at ha
  apply Subtype.ext
  exact (faithfulOn_iff.1 hf) a a.2 ha

@[expose] noncomputable def restrictRangeEquiv (hI : Invariant K I) (hf : FaithfulOn K I) :
    ↥K ≃* ↥(restrictRange K I hI) :=
  MulEquiv.ofBijective (restrictHom K I hI).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.2 (restrictHom_injective_of_faithfulOn hI hf),
      MonoidHom.rangeRestrict_surjective _⟩

@[simp] theorem coe_restrictRangeEquiv (hI : Invariant K I) (hf : FaithfulOn K I) (k : ↥K) :
    ((restrictRangeEquiv hI hf k : ↥(restrictRange K I hI)) : GLV ↥I) = restrictHom K I hI k :=
  rfl

theorem natCard_restrictRange (hI : Invariant K I) (hf : FaithfulOn K I) :
    Nat.card ↥(restrictRange K I hI) = Nat.card ↥K :=
  (Nat.card_congr (restrictRangeEquiv hI hf).toEquiv).symm

theorem eq_of_restrictRange_eq {L L₂ : Subgroup (GLV V)} (hKI : FaithfulOn K I) (hL : L ≤ K)
    (hL₂ : L₂ ≤ K) (hLI : Invariant L I) (hL₂I : Invariant L₂ I)
    (h : restrictRange L I hLI = restrictRange L₂ I hL₂I) : L = L₂ := by
  have key : ∀ {M M₂ : Subgroup (GLV V)} (hM : M ≤ K) (hM₂ : M₂ ≤ K) (hMI : Invariant M I)
      (hM₂I : Invariant M₂ I), restrictRange M I hMI ≤ restrictRange M₂ I hM₂I → M ≤ M₂ := by
    intro M M₂ hM hM₂ hMI hM₂I hle l hl
    have h1 : restrictEquiv l I (hMI.conjSub_eq hl) ∈ restrictRange M₂ I hM₂I :=
      hle (restrictEquiv_mem_restrictRange hMI hl)
    obtain ⟨l₂, hl₂, hl₂eq⟩ := (mem_restrictRange_iff hM₂I).1 h1
    have h2 : l₂⁻¹ * l ∈ K := K.mul_mem (K.inv_mem (hM₂ hl₂)) (hM hl)
    have h3 : (l₂⁻¹ * l) = 1 := by
      refine faithfulOn_iff.1 hKI _ h2 fun u hu => ?_
      have h4 : l u = l₂ u := hl₂eq ⟨u, hu⟩
      show l₂⁻¹ (l u) = u
      rw [h4]
      simp
    have : l = l₂ := by
      have := congrArg (fun g => l₂ * g) h3
      simpa using this
    rw [this]
    exact hl₂
  exact le_antisymm (key hL hL₂ hLI hL₂I h.le) (key hL₂ hL hL₂I hLI h.ge)

theorem isElemAbelian_restrictRange {A : Subgroup (GLV V)} (hA : Invariant A I)
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (restrictRange A I hA) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a₀, ha₀⟩ := a.2
    obtain ⟨b₀, hb₀⟩ := b.2
    apply Subtype.ext
    show (a : GLV ↥I) * b = b * a
    rw [← ha₀, ← hb₀, ← map_mul, ← map_mul]
    congr 1
    exact h.1.is_comm.comm a₀ b₀
  · obtain ⟨x₀, rfl⟩ := hx
    rw [← map_pow]
    have : x₀ ^ 2 = 1 := Subtype.ext (h.2 (x₀ : GLV V) x₀.2)
    rw [this, map_one]

end Faithful

section Components

variable {Γ K L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem isComponentOf_restrictRange (hKI : Invariant K I) (hLI : Invariant L I) (hKΓ : K ≤ Γ)
    (hLK : L ≤ K) (hf : FaithfulOn L I) (hL : IsComponentOf L Γ) :
    IsComponentOf (restrictRange L I hLI) (restrictRange K I hKI) := by
  refine ⟨restrictRange_mono hLI hKI hLK, ?_, ?_⟩
  · have h1 : IsSubnormal L K := by
      have := B113.isSubnormal_inf_of_le hL.2.1 hKΓ
      rwa [inf_of_le_right hLK] at this
    have h2 : IsSubnormal (L.subgroupOf K) ⊤ := (isSubnormal_subgroupOf_top_iff hLK).2 h1
    have h3 := CFSG.ComponentClassification.Components.chain_map (restrictHom K I hKI) h2
    have e1 : (L.subgroupOf K).map (restrictHom K I hKI) = restrictRange L I hLI := by
      ext g
      rw [Subgroup.mem_map, mem_restrictRange_iff hLI]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨(k : GLV V), hk, fun i => rfl⟩
      · rintro ⟨l, hl, hgl⟩
        refine ⟨⟨l, hLK hl⟩, hl, ?_⟩
        ext i
        exact (hgl i).symm
    have e2 : (⊤ : Subgroup ↥K).map (restrictHom K I hKI) = restrictRange K I hKI := by
      rw [← MonoidHom.range_eq_map]
      rfl
    rwa [e1, e2] at h3
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (restrictRangeEquiv hLI hf).symm hL.2.2

end Components

end G11

end CFSG.Quasithin
