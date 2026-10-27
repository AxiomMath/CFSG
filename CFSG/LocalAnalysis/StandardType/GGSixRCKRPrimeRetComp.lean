module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetCompFin
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
import CFSG.LieType.Chevalley.BruhatCellFactorization

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Timmesfeld
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem rckCu_glue {G N : Type*} [Group G] [Group N] {ι : Type*} [Nonempty ι]
    (r : ι → ι → Prop) (T : ι → Subgroup G) (hdir : ∀ i j, ∃ k, r i k ∧ r j k)
    (hmono : ∀ i j, r i j → T i ≤ T j) (F : ∀ i, ↥(T i) →* N)
    (hcompat : ∀ i j (h : r i j) (x : ↥(T i)), F j ⟨(x : G), hmono i j h x.2⟩ = F i x)
    (H : Subgroup G) (hH : ∀ x : G, x ∈ H ↔ ∃ i, x ∈ T i) :
    ∃ θ : ↥H →* N, ∀ i (x : ↥(T i)), θ ⟨(x : G), (hH _).2 ⟨i, x.2⟩⟩ = F i x := by
  classical
  have hex : ∀ x : ↥H, ∃ i, (x : G) ∈ T i := fun x => (hH _).1 x.2
  choose idx hidx using hex
  have key : ∀ (x : ↥H) (i : ι) (hi : (x : G) ∈ T i),
      F i ⟨(x : G), hi⟩ = F (idx x) ⟨(x : G), hidx x⟩ := by
    intro x i hi
    obtain ⟨k, hik, hjk⟩ := hdir i (idx x)
    exact (hcompat i k hik ⟨(x : G), hi⟩).symm.trans
      (hcompat (idx x) k hjk ⟨(x : G), hidx x⟩)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨{ toFun := fun x => F (idx x) ⟨(x : G), hidx x⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · show F (idx 1) ⟨((1 : ↥H) : G), hidx 1⟩ = 1
    rw [← key 1 i₀ (one_mem _)]
    exact map_one (F i₀)
  · intro x y
    obtain ⟨k, hxk, hyk⟩ := hdir (idx x) (idx y)
    have hx' : (x : G) ∈ T k := hmono _ _ hxk (hidx x)
    have hy' : (y : G) ∈ T k := hmono _ _ hyk (hidx y)
    show F (idx (x * y)) ⟨((x * y : ↥H) : G), hidx (x * y)⟩ =
      F (idx x) ⟨(x : G), hidx x⟩ * F (idx y) ⟨(y : G), hidx y⟩
    rw [← key (x * y) k (mul_mem hx' hy'), ← key x k hx', ← key y k hy', ← map_mul]
    rfl
  · intro i x
    exact (key ⟨(x : G), (hH _).2 ⟨i, x.2⟩⟩ i x.2).symm

theorem rckCu_exists_lift_map {G₁ G₂ N : Type*} [Group G₁] [Group G₂] [Group N]
    (b : G₁ →* G₂) (hb : Function.Injective b) (A : Subgroup G₁) (F : ↥A →* N) :
    ∃ f : ↥(A.map b) →* N,
      ∀ (g : G₁) (hg : g ∈ A), f ⟨b g, Subgroup.mem_map_of_mem b hg⟩ = F ⟨g, hg⟩ := by
  refine ⟨F.comp (Subgroup.equivMapOfInjective A b hb).symm.toMonoidHom, fun g hg => ?_⟩
  have h : (Subgroup.equivMapOfInjective A b hb).symm ⟨b g, Subgroup.mem_map_of_mem b hg⟩ =
      ⟨g, hg⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  show F ((Subgroup.equivMapOfInjective A b hb).symm ⟨b g, Subgroup.mem_map_of_mem b hg⟩) = _
  rw [h]

theorem rckCu_exists_fin (S : Finset GGL) :
    ∃ K : {K : Subfield GGL // Finite ↥K}, (S : Set GGL) ⊆ (K.1 : Set GGL) := by
  obtain ⟨E, hE, hSE, -⟩ :=
    CFSG.LieType.Chevalley.exists_finite_subfield_of_finset (K := ZMod 2) (L := GGL) S
  exact ⟨⟨E, hE⟩, hSE⟩

theorem rckCu_dir (K₁ K₂ : {K : Subfield GGL // Finite ↥K}) :
    ∃ K₃ : {K : Subfield GGL // Finite ↥K}, K₁.1 ≤ K₃.1 ∧ K₂.1 ≤ K₃.1 := by
  haveI := K₁.2
  haveI := K₂.2
  have h1 : (K₁.1 : Set GGL).Finite := Set.toFinite _
  have h2 : (K₂.1 : Set GGL).Finite := Set.toFinite _
  obtain ⟨K₃, hK₃⟩ := rckCu_exists_fin (h1.union h2).toFinset
  refine ⟨K₃, fun x hx => hK₃ ?_, fun x hx => hK₃ ?_⟩
  · exact (Set.Finite.mem_toFinset _).2 (Or.inl hx)
  · exact (Set.Finite.mem_toFinset _).2 (Or.inr hx)

theorem rckCu_baseChangeGL_comp
    {τ : Tag} {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C)
    {S : Set (Fin τ.rank → ℤ)} {x : ModGL τ A} (hx : x ∈ rootSpan τ A S) :
    baseChangeGL g (baseChangeGL f x) = baseChangeGL (g.comp f) x := by
  refine rckRet_rootSpan_induction (R := A) (S := S)
    (P := fun y _ => baseChangeGL g (baseChangeGL f y) = baseChangeGL (g.comp f) y) ?_ ?_ ?_ hx
  · intro α _ c _
    rw [baseChangeGL_pinnedX, baseChangeGL_pinnedX, baseChangeGL_pinnedX]
    rfl
  · rw [map_one, map_one, map_one]
  · intro y z _ _ h1 h2
    simp only [map_mul, h1, h2]

theorem rckCu_map_le
    {τ : Tag} {A B : Type} [Field A] [Field B] (f : A →+* B) (T : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ A T).map (baseChangeGL f) ≤ rootSpan τ B T := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  show baseChangeGL f (pinnedX τ A γ c) ∈ rootSpan τ B T
  rw [baseChangeGL_pinnedX]
  exact pinnedX_mem_rootSpan hγ _

theorem rckCu_incl
    {τ : Tag} {K₁ K₃ : Subfield GGL} (h : K₁ ≤ K₃) {S : Set (Fin τ.rank → ℤ)}
    {g : ModGL τ ↥K₁} (hg : g ∈ rootSpan τ ↥K₁ S) :
    baseChangeGL (Subfield.inclusion h) g ∈ rootSpan τ ↥K₃ S ∧
      baseChangeGL K₃.subtype (baseChangeGL (Subfield.inclusion h) g) =
        baseChangeGL K₁.subtype g := by
  refine ⟨rckCu_map_le (Subfield.inclusion h) S ⟨g, hg, rfl⟩, ?_⟩
  rw [rckCu_baseChangeGL_comp _ _ hg]
  have e : K₃.subtype.comp (Subfield.inclusion h) = K₁.subtype := RingHom.ext fun _ => rfl
  rw [e]

theorem rckCu_map_mono
    {τ : Tag} (S : Set (Fin τ.rank → ℤ)) {K₁ K₂ : Subfield GGL} (h : K₁ ≤ K₂) :
    (rootSpan τ ↥K₁ S).map (baseChangeGL K₁.subtype) ≤
      (rootSpan τ ↥K₂ S).map (baseChangeGL K₂.subtype) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨hg', hbc⟩ := rckCu_incl h hg
  exact Subgroup.mem_map.2 ⟨_, hg', hbc⟩

theorem rckCu_mem_iff
    {τ : Tag} (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ GGL) :
    x ∈ rootSpan τ GGL S ↔ ∃ K : {K : Subfield GGL // Finite ↥K},
      x ∈ (rootSpan τ ↥K.1 S).map (baseChangeGL K.1.subtype) := by
  constructor
  · intro hx
    refine rckRet_rootSpan_induction (R := GGL) (S := S)
      (P := fun y _ => ∃ K : {K : Subfield GGL // Finite ↥K},
        y ∈ (rootSpan τ ↥K.1 S).map (baseChangeGL K.1.subtype)) ?_ ?_ ?_ hx
    · intro α hα c _
      obtain ⟨K', hK'⟩ := rckCu_exists_fin {c}
      have hc : c ∈ K'.1 := hK' (by simp)
      refine ⟨K', Subgroup.mem_map.2 ⟨pinnedX τ ↥K'.1 α ⟨c, hc⟩, pinnedX_mem_rootSpan hα _, ?_⟩⟩
      rw [baseChangeGL_pinnedX]
      rfl
    · obtain ⟨K', -⟩ := rckCu_exists_fin ∅
      exact ⟨K', one_mem _⟩
    · rintro y z - - ⟨K₁, hy⟩ ⟨K₂, hz⟩
      obtain ⟨K₃, h13, h23⟩ := rckCu_dir K₁ K₂
      exact ⟨K₃, mul_mem (rckCu_map_mono S h13 hy) (rckCu_map_mono S h23 hz)⟩
  · rintro ⟨K, hK⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hK
    exact rckCu_map_le K.1.subtype S ⟨g, hg, rfl⟩

@[expose] noncomputable def rckCu_phi
    {τ : Tag} (K : Subfield GGL) (G : Subgroup (ModGL τ ↥K))
    (θ : ↥G →* ↥(adjointGroup Tag.E6 ↥K)) : ↥G →* ModGL Tag.E6 GGL :=
  ((baseChangeGL (τ := Tag.E6) K.subtype).comp (adjointGroup Tag.E6 ↥K).subtype).comp θ

theorem rckCu_phi_apply
    {τ : Tag} (K : Subfield GGL) (G : Subgroup (ModGL τ ↥K))
    (θ : ↥G →* ↥(adjointGroup Tag.E6 ↥K)) (x : ↥G) :
    rckCu_phi K G θ x =
      baseChangeGL K.subtype ((θ x : ↥(adjointGroup Tag.E6 ↥K)) : ModGL Tag.E6 ↥K) := rfl

@[expose] noncomputable def rckCu_inclHom
    {τ : Tag} {K₁ K₃ : Subfield GGL} (h : K₁ ≤ K₃) (S : Set (Fin τ.rank → ℤ)) :
    ↥(rootSpan τ ↥K₁ S) →* ↥(rootSpan τ ↥K₃ S) :=
  ((baseChangeGL (τ := τ) (Subfield.inclusion h)).comp (rootSpan τ ↥K₁ S).subtype).codRestrict
    (rootSpan τ ↥K₃ S) fun x => (rckCu_incl h x.2).1

theorem rckCu_phi_compat
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} {K₁ K₃ : Subfield GGL} (h : K₁ ≤ K₃)
    (θ₁ : ↥(rootSpan τ ↥K₁ (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 ↥K₁))
    (θ₃ : ↥(rootSpan τ ↥K₃ (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 ↥K₃))
    (h₁ : ∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : ↥K₁)
      (hm : pinnedX τ ↥K₁ γ c ∈ rootSpan τ ↥K₁ (rootsOfFam β Set.univ)),
      ((θ₁ ⟨pinnedX τ ↥K₁ γ c, hm⟩ : ↥(adjointGroup Tag.E6 ↥K₁)) : ModGL Tag.E6 ↥K₁) =
        pinnedX Tag.E6 ↥K₁ (ι γ) c)
    (h₃ : ∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : ↥K₃)
      (hm : pinnedX τ ↥K₃ γ c ∈ rootSpan τ ↥K₃ (rootsOfFam β Set.univ)),
      ((θ₃ ⟨pinnedX τ ↥K₃ γ c, hm⟩ : ↥(adjointGroup Tag.E6 ↥K₃)) : ModGL Tag.E6 ↥K₃) =
        pinnedX Tag.E6 ↥K₃ (ι γ) c) :
    (rckCu_phi K₃ _ θ₃).comp (rckCu_inclHom h _) = rckCu_phi K₁ _ θ₁ := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, hy⟩ := x
  refine rckRet_rootSpan_induction (R := ↥K₁) (S := rootsOfFam β Set.univ)
    (P := fun y hy => ((rckCu_phi K₃ _ θ₃).comp (rckCu_inclHom h _)) ⟨y, hy⟩ =
      rckCu_phi K₁ _ θ₁ ⟨y, hy⟩) ?_ ?_ ?_ hy
  · intro α hα c hm
    have e : rckCu_inclHom h (rootsOfFam β Set.univ) ⟨pinnedX τ ↥K₁ α c, hm⟩ =
        ⟨pinnedX τ ↥K₃ α (Subfield.inclusion h c), pinnedX_mem_rootSpan hα _⟩ :=
      Subtype.ext (baseChangeGL_pinnedX _ _ _)
    show rckCu_phi K₃ _ θ₃ (rckCu_inclHom h _ ⟨pinnedX τ ↥K₁ α c, hm⟩) = _
    rw [e, rckCu_phi_apply, rckCu_phi_apply, h₃ α hα _ _, h₁ α hα c hm, baseChangeGL_pinnedX,
      baseChangeGL_pinnedX]
    rfl
  · show rckCu_phi K₃ _ θ₃ (rckCu_inclHom h _ 1) = rckCu_phi K₁ _ θ₁ 1
    rw [map_one, map_one, map_one]
  · intro y z hy hz h1 h2
    show rckCu_phi K₃ _ θ₃ (rckCu_inclHom h _ (⟨y, hy⟩ * ⟨z, hz⟩)) =
      rckCu_phi K₁ _ θ₁ (⟨y, hy⟩ * ⟨z, hz⟩)
    simp only [map_mul]
    exact congrArg₂ (· * ·) h1 h2

structure RetFinCmp
    {τ : Tag} (β : Fin 6 → Fin τ.rank → ℤ)
    (ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) where
  θK : ∀ K' : Subfield GGL, Finite ↥K' →
    ↥(rootSpan τ ↥K' (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 ↥K')
  gen : ∀ (K' : Subfield GGL) (hK' : Finite ↥K'), ∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : ↥K')
    (hm : pinnedX τ ↥K' γ c ∈ rootSpan τ ↥K' (rootsOfFam β Set.univ)),
    ((θK K' hK' ⟨pinnedX τ ↥K' γ c, hm⟩ : ↥(adjointGroup Tag.E6 ↥K')) : ModGL Tag.E6 ↥K') =
      pinnedX Tag.E6 ↥K' (ι γ) c
  surj : ∀ (K' : Subfield GGL) (hK' : Finite ↥K'), Function.Surjective (θK K' hK')
  ker : ∀ (K' : Subfield GGL) (hK' : Finite ↥K'), ∀ x, θK K' hK' x = 1 →
    x ∈ Subgroup.center ↥(rootSpan τ ↥K' (rootsOfFam β Set.univ))

@[expose] def RetGlued
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι)
    (θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL) : Prop :=
  ∀ (x : ↥(RetH τ β)) (K : {K : Subfield GGL // Finite ↥K}) (g : ModGL τ ↥K.1)
    (hg : g ∈ rootSpan τ ↥K.1 (rootsOfFam β Set.univ)),
    (x : ModGL τ GGL) = baseChangeGL K.1.subtype g →
    θ x = baseChangeGL K.1.subtype
      ((D.θK K.1 K.2 ⟨g, hg⟩ : ↥(adjointGroup Tag.E6 ↥K.1)) : ModGL Tag.E6 ↥K.1)

theorem rckCu_inclHom_val
    {τ : Tag} {K₁ K₃ : Subfield GGL} (h : K₁ ≤ K₃) (S : Set (Fin τ.rank → ℤ))
    (x : ↥(rootSpan τ ↥K₁ S)) :
    ((rckCu_inclHom h S x : ↥(rootSpan τ ↥K₃ S)) : ModGL τ ↥K₃) =
      baseChangeGL (Subfield.inclusion h) (x : ModGL τ ↥K₁) := rfl

theorem rckCu_phi_compat_apply
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} {K₁ K₃ : Subfield GGL} (h : K₁ ≤ K₃)
    (θ₁ : ↥(rootSpan τ ↥K₁ (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 ↥K₁))
    (θ₃ : ↥(rootSpan τ ↥K₃ (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 ↥K₃))
    (h₁ : ∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : ↥K₁)
      (hm : pinnedX τ ↥K₁ γ c ∈ rootSpan τ ↥K₁ (rootsOfFam β Set.univ)),
      ((θ₁ ⟨pinnedX τ ↥K₁ γ c, hm⟩ : ↥(adjointGroup Tag.E6 ↥K₁)) : ModGL Tag.E6 ↥K₁) =
        pinnedX Tag.E6 ↥K₁ (ι γ) c)
    (h₃ : ∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : ↥K₃)
      (hm : pinnedX τ ↥K₃ γ c ∈ rootSpan τ ↥K₃ (rootsOfFam β Set.univ)),
      ((θ₃ ⟨pinnedX τ ↥K₃ γ c, hm⟩ : ↥(adjointGroup Tag.E6 ↥K₃)) : ModGL Tag.E6 ↥K₃) =
        pinnedX Tag.E6 ↥K₃ (ι γ) c)
    (g : ModGL τ ↥K₁) (hg : g ∈ rootSpan τ ↥K₁ (rootsOfFam β Set.univ)) :
    rckCu_phi K₃ _ θ₃ ⟨baseChangeGL (Subfield.inclusion h) g, (rckCu_incl h hg).1⟩ =
      rckCu_phi K₁ _ θ₁ ⟨g, hg⟩ := by
  have h1 := DFunLike.congr_fun (rckCu_phi_compat h θ₁ θ₃ h₁ h₃) ⟨g, hg⟩
  have h0 : ((rckCu_phi K₃ _ θ₃).comp (rckCu_inclHom h _)) ⟨g, hg⟩ =
      rckCu_phi K₃ _ θ₃ (rckCu_inclHom h _ ⟨g, hg⟩) := rfl
  have e : rckCu_inclHom h (rootsOfFam β Set.univ) ⟨g, hg⟩ =
      ⟨baseChangeGL (Subfield.inclusion h) g, (rckCu_incl h hg).1⟩ :=
    Subtype.ext (rckCu_inclHom_val h _ ⟨g, hg⟩)
  rw [e] at h0
  exact h0.symm.trans h1

theorem rckCu_Fh_exists
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι) :
    ∃ Fh : ∀ K' : {K : Subfield GGL // Finite ↥K},
        ↥((rootSpan τ ↥K'.1 (rootsOfFam β Set.univ)).map (baseChangeGL K'.1.subtype)) →*
          ModGL Tag.E6 GGL,
      ∀ (K' : {K : Subfield GGL // Finite ↥K}) (g : ModGL τ ↥K'.1)
        (hg : g ∈ rootSpan τ ↥K'.1 (rootsOfFam β Set.univ)),
        Fh K' ⟨baseChangeGL K'.1.subtype g, Subgroup.mem_map_of_mem _ hg⟩ =
          rckCu_phi K'.1 _ (D.θK K'.1 K'.2) ⟨g, hg⟩ := by
  choose Fh hFh using fun K' : {K : Subfield GGL // Finite ↥K} =>
    rckCu_exists_lift_map (baseChangeGL K'.1.subtype) (baseChangeGL_injective _)
      (rootSpan τ ↥K'.1 (rootsOfFam β Set.univ)) (rckCu_phi K'.1 _ (D.θK K'.1 K'.2))
  exact ⟨Fh, hFh⟩

theorem rckCu_Fh_compat
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι)
    (Fh : ∀ K' : {K : Subfield GGL // Finite ↥K},
        ↥((rootSpan τ ↥K'.1 (rootsOfFam β Set.univ)).map (baseChangeGL K'.1.subtype)) →*
          ModGL Tag.E6 GGL)
    (hFh : ∀ (K' : {K : Subfield GGL // Finite ↥K}) (g : ModGL τ ↥K'.1)
        (hg : g ∈ rootSpan τ ↥K'.1 (rootsOfFam β Set.univ)),
        Fh K' ⟨baseChangeGL K'.1.subtype g, Subgroup.mem_map_of_mem _ hg⟩ =
          rckCu_phi K'.1 _ (D.θK K'.1 K'.2) ⟨g, hg⟩)
    (K₁ K₂ : {K : Subfield GGL // Finite ↥K}) (h : K₁.1 ≤ K₂.1)
    (x : ↥((rootSpan τ ↥K₁.1 (rootsOfFam β Set.univ)).map (baseChangeGL K₁.1.subtype))) :
    Fh K₂ ⟨(x : ModGL τ GGL), rckCu_map_mono _ h x.2⟩ = Fh K₁ x := by
  obtain ⟨_, g, hg, rfl⟩ := x
  obtain ⟨hg', hbc⟩ := rckCu_incl h hg
  have e : (⟨baseChangeGL K₁.1.subtype g, rckCu_map_mono _ h (Subgroup.mem_map_of_mem _ hg)⟩ :
      ↥((rootSpan τ ↥K₂.1 (rootsOfFam β Set.univ)).map (baseChangeGL K₂.1.subtype))) =
      ⟨baseChangeGL K₂.1.subtype (baseChangeGL (Subfield.inclusion h) g),
        Subgroup.mem_map_of_mem _ hg'⟩ := Subtype.ext hbc.symm
  have e1 := hFh K₁ g hg
  have e2 := hFh K₂ _ hg'
  have e3 := rckCu_phi_compat_apply h (D.θK K₁.1 K₁.2) (D.θK K₂.1 K₂.2)
    (D.gen K₁.1 K₁.2) (D.gen K₂.1 K₂.2) g hg
  exact (congrArg (Fh K₂) e).trans (e2.trans (e3.trans e1.symm))

theorem rckCu_exists_glued
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι) :
    ∃ θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL, RetGlued D θ := by
  haveI : Nonempty {K : Subfield GGL // Finite ↥K} := by
    obtain ⟨K', -⟩ := rckCu_exists_fin ∅
    exact ⟨K'⟩
  obtain ⟨Fh, hFh⟩ := rckCu_Fh_exists D
  obtain ⟨θ, hθ⟩ := rckCu_glue (ι := {K : Subfield GGL // Finite ↥K})
    (fun K₁ K₂ => K₁.1 ≤ K₂.1)
    (fun K' => (rootSpan τ ↥K'.1 (rootsOfFam β Set.univ)).map (baseChangeGL K'.1.subtype))
    rckCu_dir (fun K₁ K₂ h => rckCu_map_mono _ h) Fh (rckCu_Fh_compat D Fh hFh) (RetH τ β)
    (fun x => rckCu_mem_iff _ x)
  refine ⟨θ, ?_⟩
  rintro ⟨x, hx⟩ K' g hg rfl
  exact (hθ K' ⟨baseChangeGL K'.1.subtype g, Subgroup.mem_map_of_mem _ hg⟩).trans (hFh K' g hg)

theorem rckCu_spec_gen
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetGlued D θ) :
    ∀ γ ∈ rootsOfFam β Set.univ, ∀ c : GGL, ∀ hm : pinnedX τ GGL γ c ∈ RetH τ β,
      θ ⟨pinnedX τ GGL γ c, hm⟩ = pinnedX Tag.E6 GGL (ι γ) c := by
  intro γ hγ c hm
  obtain ⟨K', hK'⟩ := rckCu_exists_fin {c}
  have hc : c ∈ K'.1 := hK' (by simp)
  have hg : pinnedX τ ↥K'.1 γ ⟨c, hc⟩ ∈ rootSpan τ ↥K'.1 (rootsOfFam β Set.univ) :=
    pinnedX_mem_rootSpan hγ _
  have e1 : baseChangeGL K'.1.subtype (pinnedX τ ↥K'.1 γ ⟨c, hc⟩) = pinnedX τ GGL γ c :=
    baseChangeGL_pinnedX _ _ _
  rw [hθ ⟨_, hm⟩ K' _ hg e1.symm, D.gen K'.1 K'.2 γ hγ ⟨c, hc⟩ hg, baseChangeGL_pinnedX]
  rfl

theorem rckCu_spec_range
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL}
    (hgen : ∀ γ ∈ rootsOfFam β Set.univ, ∀ c : GGL, ∀ hm : pinnedX τ GGL γ c ∈ RetH τ β,
      θ ⟨pinnedX τ GGL γ c, hm⟩ = pinnedX Tag.E6 GGL (ι γ) c) :
    θ.range = adjointGroup Tag.E6 GGL := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    refine rckRet_rootSpan_induction (R := GGL) (S := rootsOfFam β Set.univ)
      (P := fun y hy => θ ⟨y, hy⟩ ∈ adjointGroup Tag.E6 GGL) ?_ ?_ ?_ hx
    · intro α hα c hm
      rw [hgen α hα c hm]
      exact pinnedX_mem_adjointGroup _ _
    · show θ 1 ∈ _
      rw [map_one]
      exact one_mem _
    · intro y z hy hz h1 h2
      show θ (⟨y, hy⟩ * ⟨z, hz⟩) ∈ _
      rw [map_mul]
      exact mul_mem h1 h2
  · rw [adjointGroup_eq_rootSpan]
    refine iSup₂_le fun γ' hγ' => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := hι.1.surjOn hγ'
    exact ⟨⟨pinnedX τ GGL γ c, pinnedX_mem_rootSpan hγ c⟩, hgen γ hγ c _⟩

theorem rckCu_two_common
    {τ : Tag} (S : Set (Fin τ.rank → ℤ)) {x y : ModGL τ GGL}
    (hx : x ∈ rootSpan τ GGL S) (hy : y ∈ rootSpan τ GGL S) :
    ∃ (K : {K : Subfield GGL // Finite ↥K}) (g₁ g₂ : ModGL τ ↥K.1),
      g₁ ∈ rootSpan τ ↥K.1 S ∧ g₂ ∈ rootSpan τ ↥K.1 S ∧
      x = baseChangeGL K.1.subtype g₁ ∧ y = baseChangeGL K.1.subtype g₂ := by
  obtain ⟨K₁, hK₁⟩ := (rckCu_mem_iff S x).1 hx
  obtain ⟨K₂, hK₂⟩ := (rckCu_mem_iff S y).1 hy
  obtain ⟨K₃, h13, h23⟩ := rckCu_dir K₁ K₂
  obtain ⟨g₁, hg₁, rfl⟩ := Subgroup.mem_map.1 hK₁
  obtain ⟨g₂, hg₂, rfl⟩ := Subgroup.mem_map.1 hK₂
  obtain ⟨hg₁', hbc₁⟩ := rckCu_incl h13 hg₁
  obtain ⟨hg₂', hbc₂⟩ := rckCu_incl h23 hg₂
  exact ⟨K₃, _, _, hg₁', hg₂', hbc₁.symm, hbc₂.symm⟩

theorem rckCu_comm_of_bc
    {τ : Tag} {K : Subfield GGL} {g₁ g₂ : ModGL τ ↥K} (h : g₂ * g₁ = g₁ * g₂) :
    baseChangeGL K.subtype g₂ * baseChangeGL K.subtype g₁ =
      baseChangeGL K.subtype g₁ * baseChangeGL K.subtype g₂ := by
  rw [← map_mul, ← map_mul, h]

theorem rckCu_spec_center
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetGlued D θ) :
    ∀ x : ↥(RetH τ β), θ x = 1 → x ∈ Subgroup.center ↥(RetH τ β) := by
  intro x hx1
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨K, g₁, g₂, hg₁, hg₂, hxK, hyK⟩ := rckCu_two_common _ x.2 y.2
  have h1 := hθ x K g₁ hg₁ hxK
  have h2 : (D.θK K.1 K.2 ⟨g₁, hg₁⟩ : ↥(adjointGroup Tag.E6 ↥K.1)) = 1 := by
    refine Subtype.ext (baseChangeGL_injective K.1.subtype ?_)
    rw [← h1, hx1]
    exact (map_one _).symm
  have h3 := Subgroup.mem_center_iff.1 (D.ker K.1 K.2 _ h2) ⟨g₂, hg₂⟩
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hxK, hyK]
  exact rckCu_comm_of_bc (congrArg Subtype.val h3)

theorem rckCu_spec_img
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (D : RetFinCmp β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetGlued D θ)
    (K'' : Subfield GGL) (hK'' : Finite ↥K'') :
    (((rootSpan τ ↥K'' (rootsOfFam β Set.univ)).map (baseChangeGL K''.subtype)).subgroupOf
      (RetH τ β)).map θ = (adjointGroup Tag.E6 ↥K'').map (baseChangeGL K''.subtype) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxmem, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨g, hg, hxg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxmem)
    rw [hθ x ⟨K'', hK''⟩ g hg hxg.symm]
    exact ⟨_, (D.θK K'' hK'' ⟨g, hg⟩).2, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨⟨g, hg⟩, hgu⟩ := D.surj K'' hK'' ⟨u, hu⟩
    have hx : baseChangeGL K''.subtype g ∈ RetH τ β :=
      rckCu_map_le K''.subtype _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨baseChangeGL K''.subtype g, hx⟩,
      Subgroup.mem_subgroupOf.2 ⟨g, hg, rfl⟩, ?_⟩
    rw [hθ ⟨_, hx⟩ ⟨K'', hK''⟩ g hg rfl, hgu]

theorem rckCu_main
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    (D : RetFinCmp β ι) :
    ∃ θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL, RetCompSpec β ι θ := by
  obtain ⟨θ, hθ⟩ := rckCu_exists_glued D
  have hgen := rckCu_spec_gen D hθ
  exact ⟨θ, hgen, rckCu_spec_range hι hgen, rckCu_spec_center D hθ,
    fun K'' hK'' => rckCu_spec_img D hθ K'' hK''⟩

theorem rckE6_comparison
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin 6 → Fin τ.rank → ℤ} (hroot : ∀ b, IsRoot τ (β b))
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι) :
    ∃ θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL, RetCompSpec β ι θ := by
  classical
  have key : ∀ K' : Subfield GGL, Finite ↥K' →
      ∃ θK : ↥(rootSpan τ ↥K' (rootsOfFam β Set.univ)) →* ↥(adjointGroup Tag.E6 ↥K'),
        (∀ γ ∈ rootsOfFam β Set.univ, ∀ (c : ↥K')
          (hm : pinnedX τ ↥K' γ c ∈ rootSpan τ ↥K' (rootsOfFam β Set.univ)),
          ((θK ⟨pinnedX τ ↥K' γ c, hm⟩ : ↥(adjointGroup Tag.E6 ↥K')) : ModGL Tag.E6 ↥K') =
            pinnedX Tag.E6 ↥K' (ι γ) c) ∧
        Function.Surjective θK ∧
        (∀ x, θK x = 1 → x ∈ Subgroup.center ↥(rootSpan τ ↥K' (rootsOfFam β Set.univ))) := by
    intro K' hK'
    haveI : Finite ↥K' := hK'
    haveI : CharP ↥K' 2 := (RingHom.charP_iff K'.subtype K'.subtype.injective 2).2 inferInstance
    obtain ⟨θK, h1, h2, h3, -⟩ := rckE6_theta_fin hτ hroot hι ↥K'
    exact ⟨θK, h1, h2, h3⟩
  choose θK hgen hsurj hker using key
  exact rckCu_main hι ⟨θK, hgen, hsurj, hker⟩

end CFSG.StandardType.RCKRP

end
