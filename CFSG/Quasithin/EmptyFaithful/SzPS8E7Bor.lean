module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Background.GoldschmidtS146RPair
public import CFSG.Quasithin.EmptyFaithful.SzPS8Ovg
public import CFSG.Quasithin.EmptyFaithful.SzPS8Sylow
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits

namespace SzPS8

section Generic

theorem map_normalizer_eq {G : Type} [Group G] {L S : Subgroup G} (hSL : S ≤ L) {Q : Type*}
    [Group Q] (ε : ↥L →* Q) (hker : ∀ x : ↥L, ε x = 1 → (x : G) ∈ S) :
    ((L ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L).map ε =
      Subgroup.normalizer (((S.subgroupOf L).map ε : Subgroup Q) : Set Q) ⊓ ε.range := by
  classical
  set S₀ : Subgroup ↥L := S.subgroupOf L with hS₀
  set P : Subgroup Q := S₀.map ε with hP
  have hfwd : ∀ b : ↥L, (∀ g : G, g ∈ S ↔ (b : G) * g * (b : G)⁻¹ ∈ S) →
      ∀ y ∈ P, ε b * y * (ε b)⁻¹ ∈ P := by
    intro b hb y hy
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨b * s * b⁻¹, ?_, by simp⟩
    show ((b * s * b⁻¹ : ↥L) : G) ∈ S
    simpa using (hb (s : G)).mp hs
  have hkey : ∀ c : ↥L, ε c ∈ Subgroup.normalizer (P : Set Q) →
      ∀ s : ↥L, (s : G) ∈ S → ((c * s * c⁻¹ : ↥L) : G) ∈ S := by
    intro c hc s hs
    have h1 : ε c * ε s * (ε c)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hc (ε s)).mp ⟨s, hs, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := h1
    have h3 : ε (s'⁻¹ * (c * s * c⁻¹)) = 1 := by
      rw [map_mul, map_inv, hs'e, map_mul, map_mul, map_inv]
      group
    have h4 : ((s'⁻¹ * (c * s * c⁻¹) : ↥L) : G) ∈ S := hker _ h3
    have h5 : ((c * s * c⁻¹ : ↥L) : G) = (s' : G) * ((s'⁻¹ * (c * s * c⁻¹) : ↥L) : G) := by
      simp
    rw [h5]
    exact S.mul_mem hs' h4
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, ⟨b, rfl⟩⟩
    have hbn : ∀ g : G, g ∈ S ↔ (b : G) * g * (b : G)⁻¹ ∈ S :=
      Subgroup.mem_normalizer_iff.mp hb.2
    have hconj : ∀ g : G, (b : G) * ((b : G)⁻¹ * g * (b : G)) * (b : G)⁻¹ = g := by
      intro g
      group
    have hbn' : ∀ g : G, g ∈ S ↔ ((b⁻¹ : ↥L) : G) * g * ((b⁻¹ : ↥L) : G)⁻¹ ∈ S := by
      intro g
      have h := hbn ((b : G)⁻¹ * g * (b : G))
      rw [hconj g] at h
      simpa using h.symm
    show ε b ∈ Subgroup.normalizer (P : Set Q)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨hfwd b hbn y, fun hy => by
      have := hfwd b⁻¹ hbn' _ hy
      simpa [mul_assoc] using this⟩
  · rintro ⟨hx, b, rfl⟩
    refine ⟨b, ⟨b.2, ?_⟩, rfl⟩
    show (b : G) ∈ Subgroup.normalizer (S : Set G)
    rw [Subgroup.mem_normalizer_iff]
    have hcinv : ε b⁻¹ ∈ Subgroup.normalizer (P : Set Q) := by
      rw [map_inv]
      exact (Subgroup.normalizer _).inv_mem hx
    intro g
    constructor
    · intro hg
      have := hkey b hx ⟨g, hSL hg⟩ hg
      simpa using this
    · intro hg
      have hgL : (b : G) * g * (b : G)⁻¹ ∈ L := hSL hg
      have := hkey b⁻¹ hcinv ⟨_, hgL⟩ hg
      simpa [mul_assoc] using this

end Generic

section Borel

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem le_M_of_relIndex_three (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (h35 : Lemma1435)
    (h : Hyp1281Two G T M (yOfL22 T M)) {Y : Subgroup G} (hYH : Y ≤ mcOf T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hrel : (T ⊓ Y).relIndex Y = 3) : Y ≤ M := by
  classical
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hsylH : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hH : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hTYH : T ⊔ Y ≤ mcOf T := sup_le hTH hYH
  have hInH : InH T (T ⊔ Y) := by
    refine ⟨le_sup_left, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (T ⊔ Y) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hsylH).trans le_sup_left)
        (hTYH.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    intro h0
    exact hH (le_bot_iff.mp (h0 ▸ h1))
  have hrel' : T.relIndex (T ⊔ Y) = 3 := by
    rw [relIndex_sup_of_le_normalizer hTY, ← Subgroup.inf_relIndex_right]
    exact hrel
  exact le_sup_right.trans (h35 G T M hyp hnot _ hInH (Or.inl hrel'))

omit [Finite G] in
theorem conj_mem_borel {K₀ : Subgroup G} (hTN : T ≤ Subgroup.normalizer (K₀ : Set G)) {t x : G}
    (ht : t ∈ T) (hx : x ∈ K₀ ⊓ Subgroup.normalizer ((T ⊓ K₀ : Subgroup G) : Set G)) :
    t * x * t⁻¹ ∈ K₀ ⊓ Subgroup.normalizer ((T ⊓ K₀ : Subgroup G) : Set G) := by
  have hTL : ∀ t ∈ T, ∀ x, x ∈ K₀ ↔ t * x * t⁻¹ ∈ K₀ := fun t ht =>
    Subgroup.mem_normalizer_iff.mp (hTN ht)
  have hTS : ∀ t ∈ T, ∀ x, x ∈ T ⊓ K₀ ↔ t * x * t⁻¹ ∈ T ⊓ K₀ := by
    intro t ht x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), (hTL t ht x).mp hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, (hTL t ht x).mpr hxL⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
  refine ⟨(hTL t ht x).mp hx.1, ?_⟩
  show t * x * t⁻¹ ∈ Subgroup.normalizer ((T ⊓ K₀ : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hxn := Subgroup.mem_normalizer_iff.mp hx.2
  have e1 : t * x * t⁻¹ * g * (t * x * t⁻¹)⁻¹ = t * (x * (t⁻¹ * g * t) * x⁻¹) * t⁻¹ := by group
  rw [e1, ← hTS t ht, ← hxn (t⁻¹ * g * t)]
  have := hTS t⁻¹ (T.inv_mem ht) g
  simpa using this

@[expose] noncomputable def rhoRes (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {K₀ : Subgroup G} (hK₀H : K₀ ≤ mcOf T) : ↥K₀ →* (D.V ≃ₗ[ZMod 2] D.V) :=
  (S143V.rhoH h D).comp (Subgroup.inclusion hK₀H)

@[expose] noncomputable def sImg (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {K₀ : Subgroup G} (hK₀H : K₀ ≤ mcOf T) : Subgroup (D.V ≃ₗ[ZMod 2] D.V) :=
  ((T ⊓ K₀).subgroupOf K₀).map (rhoRes h D hK₀H)

theorem borel_le_M_of_two_overgroups (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G)
    (h35 : Lemma1435) (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {K₀ : Subgroup G} (hK₀H : K₀ ≤ mcOf T) (hTN : T ≤ Subgroup.normalizer (K₀ : Set G))
    (hker : ∀ x : ↥(mcOf T), (x : G) ∈ K₀ → S143V.rhoH h D x = 1 → (x : G) ∈ T)
    {Y₁ Y₂ : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hSY₁ : sImg h D hK₀H ≤ Y₁) (hSY₂ : sImg h D hK₀H ≤ Y₂)
    (hY₁ : Y₁ ≤ Subgroup.normalizer ((sImg h D hK₀H : Subgroup (D.V ≃ₗ[ZMod 2] D.V)) :
      Set (D.V ≃ₗ[ZMod 2] D.V)) ⊓ (rhoRes h D hK₀H).range)
    (hY₂ : Y₂ ≤ Subgroup.normalizer ((sImg h D hK₀H : Subgroup (D.V ≃ₗ[ZMod 2] D.V)) :
      Set (D.V ≃ₗ[ZMod 2] D.V)) ⊓ (rhoRes h D hK₀H).range)
    (hTY₁ : ∀ (t : G) (ht : t ∈ T), S143V.rhoH h D ⟨t, h.almostSpecialHyp_g1.T_le_H ht⟩ ∈
      Subgroup.normalizer (Y₁ : Set (D.V ≃ₗ[ZMod 2] D.V)))
    (hTY₂ : ∀ (t : G) (ht : t ∈ T), S143V.rhoH h D ⟨t, h.almostSpecialHyp_g1.T_le_H ht⟩ ∈
      Subgroup.normalizer (Y₂ : Set (D.V ≃ₗ[ZMod 2] D.V)))
    (hidx₁ : (sImg h D hK₀H).relIndex Y₁ = 3) (hidx₂ : (sImg h D hK₀H).relIndex Y₂ = 3)
    (hgen : Subgroup.normalizer ((sImg h D hK₀H : Subgroup (D.V ≃ₗ[ZMod 2] D.V)) :
      Set (D.V ≃ₗ[ZMod 2] D.V)) ⊓ (rhoRes h D hK₀H).range ≤ Y₁ ⊔ Y₂) :
    K₀ ⊓ Subgroup.normalizer ((T ⊓ K₀ : Subgroup G) : Set G) ≤ M := by
  classical
  set ε := rhoRes h D hK₀H with hε
  set SK : Subgroup G := T ⊓ K₀ with hSK
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hSKK : SK ≤ K₀ := inf_le_right
  have hSKT : SK ≤ T := inf_le_left
  have hker' : ∀ x : ↥K₀, ε x = 1 → (x : G) ∈ SK := fun x hx =>
    ⟨hker (Subgroup.inclusion hK₀H x) x.2 hx, x.2⟩
  set B₀' : Subgroup ↥K₀ := (K₀ ⊓ Subgroup.normalizer (SK : Set G)).subgroupOf K₀ with hB₀'
  have hmapB : B₀'.map ε = Subgroup.normalizer ((sImg h D hK₀H : Subgroup _) : Set _) ⊓
      ε.range := map_normalizer_eq hSKK ε hker'
  have hS1 : ∀ Y : Subgroup (D.V ≃ₗ[ZMod 2] D.V), sImg h D hK₀H ≤ Y →
      SK.subgroupOf K₀ ≤ Y.comap ε ⊓ B₀' := by
    intro Y hSY x hx
    refine ⟨hSY ⟨x, hx, rfl⟩, ?_⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, Subgroup.le_normalizer
      (Subgroup.mem_subgroupOf.mp hx)⟩
  have hS3 : ∀ Y : Subgroup (D.V ≃ₗ[ZMod 2] D.V),
      Y ≤ Subgroup.normalizer ((sImg h D hK₀H : Subgroup _) : Set _) ⊓ ε.range →
      (Y.comap ε ⊓ B₀').map ε = Y := by
    intro Y hYB
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.1
    · intro y hy
      have hyB := hYB hy
      rw [← hmapB] at hyB
      obtain ⟨b, hb, rfl⟩ := hyB
      exact ⟨b, ⟨hy, hb⟩, rfl⟩
  have key : ∀ Y : Subgroup (D.V ≃ₗ[ZMod 2] D.V), sImg h D hK₀H ≤ Y →
      Y ≤ Subgroup.normalizer ((sImg h D hK₀H : Subgroup _) : Set _) ⊓ ε.range →
      (∀ (t : G) (ht : t ∈ T), S143V.rhoH h D ⟨t, hTH ht⟩ ∈ Subgroup.normalizer (Y : Set _)) →
      (sImg h D hK₀H).relIndex Y = 3 → (Y.comap ε ⊓ B₀').map K₀.subtype ≤ M := by
    intro Y hSY hYB hTY hidx
    set Yt : Subgroup ↥K₀ := Y.comap ε ⊓ B₀' with hYt
    have h1 : SK.subgroupOf K₀ ≤ Yt := hS1 Y hSY
    have h2 : ∀ k ∈ Yt, ε k = 1 → k ∈ SK.subgroupOf K₀ := fun k _ hk => hker' k hk
    have h3 : Yt.map ε = Y := hS3 Y hYB
    have h4 : (SK.subgroupOf K₀).relIndex Yt = 3 := by
      rw [relIndex_eq_relIndex_map ε h1 h2, h3]
      exact hidx
    have h5 : SK.relIndex (Yt.map K₀.subtype) = 3 := by
      have := Subgroup.relIndex_map_map_of_injective (SK.subgroupOf K₀) Yt K₀.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hSKK] at this
      rw [this, h4]
    have h6 : T ≤ Subgroup.normalizer ((Yt.map K₀.subtype : Subgroup G) : Set G) := by
      have hfwd : ∀ t ∈ T, ∀ x ∈ Yt.map K₀.subtype, t * x * t⁻¹ ∈ Yt.map K₀.subtype := by
        rintro t ht _ ⟨y, hy, rfl⟩
        have hyB : (y : G) ∈ K₀ ⊓ Subgroup.normalizer (SK : Set G) := hy.2
        have hconj := conj_mem_borel hTN ht hyB
        refine ⟨⟨t * (y : G) * t⁻¹, hconj.1⟩, ⟨?_, ?_⟩, rfl⟩
        · show ε ⟨t * (y : G) * t⁻¹, hconj.1⟩ ∈ Y
          have e : ε ⟨t * (y : G) * t⁻¹, hconj.1⟩ = S143V.rhoH h D ⟨t, hTH ht⟩ * ε y *
              (S143V.rhoH h D ⟨t, hTH ht⟩)⁻¹ := by
            have e1 : Subgroup.inclusion hK₀H ⟨t * (y : G) * t⁻¹, hconj.1⟩ =
                ⟨t, hTH ht⟩ * Subgroup.inclusion hK₀H y * ⟨t, hTH ht⟩⁻¹ := rfl
            show S143V.rhoH h D (Subgroup.inclusion hK₀H ⟨t * (y : G) * t⁻¹, hconj.1⟩) = _
            rw [e1, map_mul, map_mul, map_inv]
            rfl
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp (hTY t ht) (ε y)).mp hy.1
        · exact Subgroup.mem_subgroupOf.mpr hconj
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact ⟨hfwd t ht x, fun hx => by
        have := hfwd t⁻¹ (T.inv_mem ht) _ hx
        simpa [mul_assoc] using this⟩
    have h7 : T ⊓ Yt.map K₀.subtype = SK := by
      apply le_antisymm
      · rintro x ⟨hxT, y, -, rfl⟩
        exact ⟨hxT, y.2⟩
      · refine le_inf hSKT ?_
        have := Subgroup.map_mono (f := K₀.subtype) h1
        rwa [Subgroup.map_subgroupOf_eq_of_le hSKK] at this
    have hYtH : Yt.map K₀.subtype ≤ mcOf T := by
      rintro _ ⟨y, -, rfl⟩
      exact hK₀H y.2
    exact le_M_of_relIndex_three hyp hnot h35 h hYtH h6 (by rw [h7]; exact h5)
  have hM₁ := key Y₁ hSY₁ hY₁ hTY₁ hidx₁
  have hM₂ := key Y₂ hSY₂ hY₂ hTY₂ hidx₂
  intro b hb
  set b' : ↥K₀ := ⟨b, hb.1⟩ with hb'
  have hb'B : b' ∈ B₀' := Subgroup.mem_subgroupOf.mpr hb
  have hεb : ε b' ∈ Y₁ ⊔ Y₂ := hgen (by rw [← hmapB]; exact ⟨b', hb'B, rfl⟩)
  set J' : Subgroup ↥K₀ := (Y₁.comap ε ⊓ B₀') ⊔ (Y₂.comap ε ⊓ B₀') with hJ'
  have hJ'map : J'.map ε = Y₁ ⊔ Y₂ := by
    rw [hJ', Subgroup.map_sup, hS3 Y₁ hY₁, hS3 Y₂ hY₂]
  obtain ⟨j, hj, hjε⟩ : ε b' ∈ J'.map ε := by rw [hJ'map]; exact hεb
  have hbj : b' * j⁻¹ ∈ SK.subgroupOf K₀ :=
    Subgroup.mem_subgroupOf.mpr (hker' _ (by simp [map_mul, map_inv, hjε]))
  have hSJ : SK.subgroupOf K₀ ≤ J' := (hS1 Y₁ hSY₁).trans le_sup_left
  have hb'J : b' ∈ J' := by
    have := J'.mul_mem (hSJ hbj) hj
    simpa using this
  have hJM : J'.map K₀.subtype ≤ M := by
    rw [hJ', Subgroup.map_sup]
    exact sup_le hM₁ hM₂
  exact hJM ⟨b', hb'J, rfl⟩

end Borel

end SzPS8

end CFSG.Quasithin
