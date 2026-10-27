module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineHyp711
public import CFSG.LocalAnalysis.WeakClosure81.W19VGJR

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

@[expose] def kHatOf (Γ : Set (Subgroup (LGL 2 V))) : Subgroup (LGL 2 V) :=
  Subgroup.closure (⋃ A ∈ Γ, (A : Set (LGL 2 V)))

theorem kSub_UAOf_orbit (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A) {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) :
    kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) = ⨆ A ∈ Γ, UAOf G VA A := by
  unfold kSub
  rw [(thirteen_two_three h hrank htrans hA₀).1, iSup_image]

theorem map_projG_kSub_UAOf_orbit (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A) {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) :
    (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)).map (projG G) = kHatOf Γ := by
  have hmap : (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)).map (projG G) =
      ⨆ A ∈ Γ, A := by
    rw [kSub_UAOf_orbit h hrank htrans hA₀]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun A => iSup_congr fun hA => map_projG_wHat_sup_aHat (h.le_G A hA)
  rw [hmap, kHatOf, ← iSup_subtype'' Γ (fun A : Subgroup (LGL 2 V) => A)]
  rw [Subgroup.iSup_eq_closure]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, hi⟩⟩
  · intro hx
    obtain ⟨A, hx'⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hA, hxA⟩ := Set.mem_iUnion.mp hx'
    exact Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hxA⟩

theorem hyp73_UAOf_orbit (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) :
    Hyp73 (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)
      (pCoreOf 2 (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G))) := by
  have hhyp7 := hyp7_UAOf h hrank hA₀ (hVAle A₀ hA₀)
  have hnorm : ((vHat G).subgroupOf (⊤ : Subgroup (VG G))).Normal := normal_vHat.subgroupOf _
  have hOm : ∀ W ∈ omegaSet (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G),
      W ≤ (⊤ : Subgroup (VG G)) := fun _ _ => le_top
  have hmem : UAOf G VA A₀ ∈
      omegaSet (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) := by
    rw [(thirteen_two_three h hrank htrans hA₀).1]
    exact ⟨A₀, hA₀, rfl⟩
  exact
    { elemAbelian := hhyp7.1
      ti := hhyp7.2.2
      noncyclic := hhyp7.2.1
      abelian := (isElemAbelian_wHat (G := G) ⊤).1
      le := le_top
      normal := hnorm
      mem := hmem
      omega_le := hOm
      iSub_le := iSub_le_pCoreOf_kSub le_top
      pcore_le := pCoreOf_kSub_le_pCoreOf le_top hnorm hOm
      jnormal := pCoreOf_subgroupOf_normal le_top (kSub_subgroupOf_normal le_top hnorm hOm) }

theorem fusionOddCoreOf_kSub_UAOf_orbit (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) :
    fusionOddCoreOf (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)) = ⊥ := by
  have hnorm : ((vHat G).subgroupOf (⊤ : Subgroup (VG G))).Normal := normal_vHat.subgroupOf _
  have hOm : ∀ W ∈ omegaSet (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G),
      W ≤ (⊤ : Subgroup (VG G)) := fun _ _ => le_top
  haveI : (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)).Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp
      (kSub_subgroupOf_normal (V := UAOf G VA A₀) le_top hnorm hOm)
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  exact fusionOddCoreOf_eq_bot_of_charTwo charTwo_top_VG _

private theorem inr_mem_kSub_of_mem_kHatOf (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) {n : ↥G} (hn : (n : LGL 2 V) ∈ kHatOf Γ) :
    (SemidirectProduct.inr n : VG G) ∈
      kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) := by
  let S : Set ↥G := ⋃ A ∈ Γ, (A.subgroupOf G : Set ↥G)
  have hgen : (⋃ A ∈ Γ, (A : Set (LGL 2 V))) ⊆
      ((Subgroup.closure S).map G.subtype : Set (LGL 2 V)) := by
    intro y hy
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨A, hA, hyA⟩ := hy
    refine ⟨⟨y, h.le_G A hA hyA⟩, ?_, rfl⟩
    refine Subgroup.subset_closure ?_
    change (⟨y, h.le_G A hA hyA⟩ : ↥G) ∈ ⋃ A ∈ Γ, (A.subgroupOf G : Set ↥G)
    rw [Set.mem_iUnion₂]
    exact ⟨A, hA, hyA⟩
  have hnS : n ∈ Subgroup.closure S := by
    have h1 : (n : LGL 2 V) ∈ (Subgroup.closure S).map G.subtype :=
      ((Subgroup.closure_le (K := (Subgroup.closure S).map G.subtype)).mpr hgen) hn
    obtain ⟨m, hm, hmn⟩ := h1
    have hmn' : m = n := Subtype.ext hmn
    simpa [hmn'] using hm
  have hSle : Subgroup.closure S ≤
      (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)).comap
        (SemidirectProduct.inr : ↥G →* VG G) := by
    rw [Subgroup.closure_le]
    intro x hx
    change x ∈ ⋃ A ∈ Γ, (A.subgroupOf G : Set ↥G) at hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨A, hA, hxA⟩ := hx
    change (x : LGL 2 V) ∈ A at hxA
    refine Subgroup.mem_comap.mpr ?_
    refine le_kSub (U := UAOf G VA A) ?_ ?_
    · rw [(thirteen_two_three h hrank htrans hA₀).1]
      exact ⟨A, hA, rfl⟩
    · exact Subgroup.mem_sup_right (S := wHat G (VA A)) (mem_aHat.mpr ⟨x, hxA, rfl⟩)
  exact hSle hnS

theorem transitive_kSub_UAOf_orbit (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A) {A₀ : Subgroup (LGL 2 V)}
    (hA₀ : A₀ ∈ Γ)
    (hK : ∀ B ∈ Γ, ∃ n : ↥G, (n : LGL 2 V) ∈ kHatOf Γ ∧ B = cj (n : LGL 2 V) A₀) :
    ∀ W ∈ omegaSet (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G),
      ∃ k ∈ kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G),
        W = conjSubgroup (UAOf G VA A₀) k := by
  intro W hW
  rw [(thirteen_two_three h hrank htrans hA₀).1] at hW
  obtain ⟨B, hB, rfl⟩ := hW
  obtain ⟨n, hnk, hBn⟩ := hK B hB
  refine ⟨(SemidirectProduct.inr n⁻¹ : VG G), ?_, ?_⟩
  · rw [map_inv]
    exact Subgroup.inv_mem _ (inr_mem_kSub_of_mem_kHatOf h hrank htrans hA₀ hnk)
  · rw [conjSubgroup_UAOf_inr_inv h hA₀ n, hBn]

theorem hyp711_UAOf_orbit (h : Assumption131 G Γ VA i) (hrank : ∀ A ∈ Γ, mRank A ≤ i)
    (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ)
    (hK : ∀ B ∈ Γ, ∃ n : ↥G, (n : LGL 2 V) ∈ kHatOf Γ ∧ B = cj (n : LGL 2 V) A₀) :
    Hyp711 (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) :=
  { toHyp73 := hyp73_UAOf_orbit h hrank hVAle htrans hA₀
    oddCore := fusionOddCoreOf_kSub_UAOf_orbit h hrank htrans hA₀
    transitive := transitive_kSub_UAOf_orbit h hrank htrans hA₀ hK }

theorem mem_pCoreOf_kSub_UAOf_orbit_iff (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) {x : VG G}
    (hx : x ∈ kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)) :
    x ∈ pCoreOf 2 (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)) ↔
      projG G x ∈ pCoreOf 2 (kHatOf Γ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K1 : Subgroup (VG G) := kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)
  let Khat : Subgroup (LGL 2 V) := kHatOf Γ
  have hmap : K1.map (projG G) = Khat := map_projG_kSub_UAOf_orbit h hrank htrans hA₀
  let π : ↥K1 →* ↥Khat :=
    { toFun := fun y => ⟨projG G (y : VG G), by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem (projG G) y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp }
  have hπ : Function.Surjective π := by
    intro y
    have hy : (y : LGL 2 V) ∈ K1.map (projG G) := by
      rw [hmap]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hker_le : π.ker ≤ (vHat G).comap K1.subtype := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    refine Subgroup.mem_comap.mpr ?_
    have hy1 : projG G (y : VG G) = 1 :=
      congrArg (fun z : ↥Khat => (z : LGL 2 V)) hy
    exact ker_projG_le_vHat (MonoidHom.mem_ker.mpr hy1)
  have hker_p : IsPGroup 2 π.ker :=
    ((isElemAbelian_wHat (G := G) ⊤).isPGroup.comap_of_injective K1.subtype
      Subtype.coe_injective).to_le hker_le
  constructor
  · intro hxO
    have hxK : (⟨x, show x ∈ K1 from hx⟩ : ↥K1) ∈ pCore 2 ↥K1 := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO
      have hyx' : y = (⟨x, show x ∈ K1 from hx⟩ : ↥K1) := Subtype.ext hyx
      rwa [hyx'] at hy
    have hφ : π (⟨x, show x ∈ K1 from hx⟩ : ↥K1) ∈ pCore 2 ↥Khat :=
      CFSG.LieType.BorelTits.map_pCore_le 2 π hπ (Subgroup.mem_map_of_mem π hxK)
    change projG G x ∈ (pCore 2 ↥Khat).map Khat.subtype
    exact Subgroup.mem_map_of_mem Khat.subtype hφ
  · intro hxO
    have hNp : IsPGroup 2 ((pCore 2 ↥Khat).comap π) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥Khat)).comap_of_ker_isPGroup π hker_p
    have hNle : (pCore 2 ↥Khat).comap π ≤ pCore 2 ↥K1 :=
      CFSG.LieType.BorelTits.le_pCore 2
        (Subgroup.Normal.comap (CFSG.LieType.BorelTits.pCore_normal (r := 2)) π) hNp
    have hxN : (⟨x, show x ∈ K1 from hx⟩ : ↥K1) ∈ (pCore 2 ↥Khat).comap π := by
      refine Subgroup.mem_comap.mpr ?_
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO
      have hπy : π (⟨x, show x ∈ K1 from hx⟩ : ↥K1) = y := by
        apply Subtype.ext
        show projG G x = (y : LGL 2 V)
        exact hyx.symm
      rwa [hπy]
    change x ∈ (pCore 2 ↥K1).map K1.subtype
    exact Subgroup.mem_map_of_mem K1.subtype (hNle hxN)

end CFSG.LocalAnalysis.WeakClosure81

end
