module

public import CFSG.Quasithin.EmptyFaithful.SBc15WDefs
public import CFSG.Quasithin.EmptyFaithful.SBc15F3Prod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc15

section Embed

variable {L : Type} [Group L]

def pairFun (a b : L) : Multiplicative (ZMod 2) → L := fun q => if q = 1 then a else b

theorem Z2_inv_one : (1 : Multiplicative (ZMod 2))⁻¹ = 1 := by decide

def wrEmbed : L × L →* L ≀ᵣ Multiplicative (ZMod 2) where
  toFun p := ⟨pairFun p.1 p.2, 1⟩
  map_one' := by
    refine RegularWreathProduct.ext ?_ rfl
    funext x
    simp [pairFun]
  map_mul' p q := by
    refine RegularWreathProduct.ext ?_ (by simp)
    funext x
    show pairFun (p.1 * q.1) (p.2 * q.2) x =
      pairFun p.1 p.2 x * pairFun q.1 q.2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)
    rw [Z2_inv_one, one_mul]
    by_cases hx : x = 1 <;> simp [pairFun, hx]

theorem Z2_cases (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  revert x
  decide

theorem Z2_eq_of_ne_one (a b : Multiplicative (ZMod 2)) (hb : b ≠ 1) : a = 1 ∨ a = b := by
  revert a b
  decide

theorem wrEmbed_injective : Function.Injective (wrEmbed : L × L →* _) := by
  intro p q h
  have h1 := congrArg (fun w : L ≀ᵣ Multiplicative (ZMod 2) => w.left 1) h
  have h2 := congrArg (fun w : L ≀ᵣ Multiplicative (ZMod 2) => w.left (Multiplicative.ofAdd 1)) h
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp only [wrEmbed, MonoidHom.coe_mk, OneHom.coe_mk, pairFun, ite_true, hne, ite_false] at h1 h2
  exact Prod.ext h1 h2

theorem mem_wrPerf_top {w : L ≀ᵣ Multiplicative (ZMod 2)} :
    w ∈ wrPerf (⊤ : Subgroup L) ↔ w.right = 1 :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => trivial⟩⟩

theorem range_wrEmbed : (wrEmbed : L × L →* _).range = wrPerf (⊤ : Subgroup L) := by
  ext w
  rw [MonoidHom.mem_range, mem_wrPerf_top]
  constructor
  · rintro ⟨p, rfl⟩
    rfl
  · intro h
    refine ⟨(w.left 1, w.left (Multiplicative.ofAdd 1)), ?_⟩
    refine RegularWreathProduct.ext ?_ h.symm
    funext x
    rcases Z2_cases x with rfl | rfl
    · simp [wrEmbed, pairFun]
    · have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      simp [wrEmbed, pairFun, hne]

theorem wrPerf_top_normalizer :
    (⊤ : Subgroup (L ≀ᵣ Multiplicative (ZMod 2))) ≤
      Subgroup.normalizer ((wrPerf (⊤ : Subgroup L) : Subgroup _) : Set _) := by
  refine le_normalizer_of_forall_conj fun g _ v hv => ?_
  rw [mem_wrPerf_top] at hv ⊢
  simp [hv]

theorem index_wrPerf_top : (wrPerf (⊤ : Subgroup L)).index = 2 := by
  have h1 : wrPerf (⊤ : Subgroup L) =
      (RegularWreathProduct.rightHom :
        L ≀ᵣ Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)).ker := by
    ext w
    rw [mem_wrPerf_top, MonoidHom.mem_ker]
    rfl
  have h2 : (RegularWreathProduct.rightHom :
      L ≀ᵣ Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr fun q => ⟨RegularWreathProduct.inl q, by simp⟩
  rw [h1, Subgroup.index_ker, h2, Subgroup.card_top]
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod 2

end Embed

section Main

theorem wr_first {L : Type} [Group L] [Finite L] (T : Subgroup (L ≀ᵣ Multiplicative (ZMod 2)))
    (hT : IsSylowTwoOf T ⊤) (g : L ≀ᵣ Multiplicative (ZMod 2)) :
    ∃ k ∈ wrPerf (⊤ : Subgroup L), ∃ y ∈ T, g = k * y := by
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    have e : T.index = (T.subgroupOf ⊤).index := (Subgroup.relIndex_top_right (H := T)).symm
    rwa [← e] at h
  have hnot : ¬ T ≤ wrPerf (⊤ : Subgroup L) := by
    intro hle
    have h2 : (wrPerf (⊤ : Subgroup L)).index ∣ T.index := Subgroup.index_dvd_of_le hle
    rw [index_wrPerf_top] at h2
    exact hidx h2
  obtain ⟨t, htT, htP⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  rw [mem_wrPerf_top] at htP
  rcases Z2_eq_of_ne_one g.right t.right htP with hg | hg
  · exact ⟨g, mem_wrPerf_top.mpr hg, 1, T.one_mem, by simp⟩
  · refine ⟨g * t⁻¹, mem_wrPerf_top.mpr ?_, t, htT, by simp⟩
    simp [hg]

theorem weakW_top_of_local {L : Type} [Group L] [Finite L] (h9 : ¬ 9 ∣ Nat.card L)
    (hL : ∀ R Y : Subgroup L, IsSylowTwoOf R ⊤ → R ≤ Subgroup.normalizer (Y : Set L) →
      oTwoUpper Y = Y → Y ≠ ⊥ → ¬ 7 ∣ Nat.card Y → ∃ V : Subgroup L, LocalData R Y V) :
    WeakW L ⊤ := by
  refine ⟨fun T hT g => wr_first T hT g, ?_⟩
  intro T X hT hXP hTX hO hcard k hkP hk
  obtain ⟨a, ha⟩ := hcard
  have hinj : Function.Injective (wrEmbed : L × L →* L ≀ᵣ Multiplicative (ZMod 2)) :=
    wrEmbed_injective
  have hrange : (wrEmbed : L × L →* L ≀ᵣ Multiplicative (ZMod 2)).range =
      wrPerf (⊤ : Subgroup L) := range_wrEmbed
  set ι : L × L →* L ≀ᵣ Multiplicative (ZMod 2) := wrEmbed with hι
  set P : Subgroup (L ≀ᵣ Multiplicative (ZMod 2)) := wrPerf (⊤ : Subgroup L) with hP
  set X' : Subgroup (L × L) := X.comap ι with hX'
  set T' : Subgroup (L × L) := (T ⊓ P).comap ι with hT'
  have hXmap : X'.map ι = X :=
    Subgroup.map_comap_eq_self (by rw [hrange]; exact hXP)
  have hTmap : T'.map ι = T ⊓ P :=
    Subgroup.map_comap_eq_self (by rw [hrange]; exact inf_le_right)
  have hSylP : IsSylowTwoOf (T ⊓ P) P := A4.isSylowTwoOf_inf_normal hT le_top wrPerf_top_normalizer
  have hSylP' := A4.isSylowTwoOf_iff_maximal.mp hSylP
  have hT'S : IsSylowTwoOf T' ⊤ := by
    refine A4.isSylowTwoOf_iff_maximal.mpr ⟨le_top, ?_, fun Z _ hZ hle => ?_⟩
    · exact hSylP'.2.1.comap_of_injective ι hinj
    · have hZP : Z.map ι ≤ P := by
        rw [← hrange]
        exact Subgroup.map_le_range ι Z
      have hge : T ⊓ P ≤ Z.map ι := by
        rw [← hTmap]
        exact Subgroup.map_mono hle
      have h1 := hSylP'.2.2 (Z.map ι) hZP (hZ.map ι) hge
      intro z hz
      exact h1 (Subgroup.mem_map_of_mem ι hz)
  have hTX' : T' ≤ Subgroup.normalizer (X' : Set (L × L)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hιt : ι t ∈ T := (Subgroup.mem_comap.mp ht).1
    have := Subgroup.mem_normalizer_iff.mp (hTX hιt) (ι x)
    simpa [hX', Subgroup.mem_comap, map_mul, map_inv] using this
  have hO' : oTwoUpper X' = X' := by
    apply Subgroup.map_injective hinj
    rw [← oTwoUpper_map, hXmap, hO]
  have hcard' : Nat.card X' = 9 * 2 ^ a := by
    have h1 : Nat.card (X'.map ι) = Nat.card X' := Subgroup.card_map_of_injective hinj
    rw [hXmap, ha] at h1
    exact h1.symm
  rw [← hrange] at hkP
  obtain ⟨k', rfl⟩ := hkP
  have hmapJ : (X' ⊔ T').map ι = X ⊔ T ⊓ P := by
    rw [Subgroup.map_sup, hXmap, hTmap]
  have hpc : (pCoreOf 2 (X' ⊔ T')).map ι ≤ pCoreOf 2 (X ⊔ T ⊓ P) := by
    rw [← hmapJ]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map ι)
    exact (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)).trans
      (map_normalizer_le ι _)
  have hk' : ∀ w ∈ pCoreOf 2 (X' ⊔ T'), k' * w * k'⁻¹ ∈ T' := by
    intro w hw
    have h1 := hk (ι w) (hpc (Subgroup.mem_map_of_mem ι hw))
    show ι (k' * w * k'⁻¹) ∈ T ⊓ P
    simpa [map_mul, map_inv] using h1
  have h2 := weak_prod h9 hL hT'S hTX' hO' ⟨a, hcard'⟩ k' hk'
  rw [← hmapJ]
  exact Subgroup.mem_map_of_mem ι h2

end Main

end SBc15

end CFSG.Quasithin
