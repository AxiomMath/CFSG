module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHBruhat
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcRoots
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.SeitzReduction CFSG.StandardType CFSG.Open CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.RootSystem


private def rckJB4567_f4HighCheck : Bool :=
  (List.range (Tag.rootCertificate Tag.F4).roots.length).all fun k =>
    (!decide (height ((Tag.rootCertificate Tag.F4).root k) = height RootCentExc.f4HighRoot) ||
      (List.ofFn ((Tag.rootCertificate Tag.F4).root k) == List.ofFn RootCentExc.f4HighRoot))

private theorem rckJB4567_f4HighCheck_eq_true : rckJB4567_f4HighCheck = true := by
  decide +kernel

private theorem rckJB4567_eq_f4HighRoot {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot Tag.F4 γ) (h : height γ = height RootCentExc.f4HighRoot) :
    γ = RootCentExc.f4HighRoot := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.F4) hγ
  have hc := rckJB4567_f4HighCheck_eq_true
  simp only [rckJB4567_f4HighCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hc
  rcases hc k hk with hne | heq
  · exact absurd h (by simpa using hne)
  · exact RootCertificate.eq_of_ofFn_beq heq

private def rckJB4567_e8HighCheck : Bool :=
  (List.range (Tag.rootCertificate Tag.E8).roots.length).all fun k =>
    (!decide (height ((Tag.rootCertificate Tag.E8).root k) = height RootCentExc.e8HighRoot) ||
      (List.ofFn ((Tag.rootCertificate Tag.E8).root k) == List.ofFn RootCentExc.e8HighRoot))

private theorem rckJB4567_e8HighCheck_eq_true : rckJB4567_e8HighCheck = true := by
  decide +kernel

private theorem rckJB4567_eq_e8HighRoot {γ : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot Tag.E8 γ) (h : height γ = height RootCentExc.e8HighRoot) :
    γ = RootCentExc.e8HighRoot := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.E8) hγ
  have hc := rckJB4567_e8HighCheck_eq_true
  simp only [rckJB4567_e8HighCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hc
  rcases hc k hk with hne | heq
  · exact absurd h (by simpa using hne)
  · exact RootCertificate.eq_of_ofFn_beq heq

private theorem rckJB4567_cent_of_map_conj {M : LieUniversal}
    {β γ : Fin M.D.rank → ℤ} {g : M.K}
    (h : (M.D.rootGroup γ).map (MulAut.conj g).toMonoidHom = M.D.rootGroup β)
    (hC : RCKLemmaHCent M γ) : RCKLemmaHCent M β := by
  have hmem : ∀ z : M.K, z ∈ M.D.rootGroup β ↔ g⁻¹ * z * g ∈ M.D.rootGroup γ := by
    intro z
    have hz : z ∈ (M.D.rootGroup γ).map (MulAut.conj g).toMonoidHom ↔
        g⁻¹ * z * g ∈ M.D.rootGroup γ := by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyz⟩
        change (MulAut.conj g) y = z at hyz
        rw [MulAut.conj_apply] at hyz
        rw [← hyz]
        convert hy using 1
        group
      · intro hz
        exact ⟨g⁻¹ * z * g, hz, by
          change (MulAut.conj g) (g⁻¹ * z * g) = z
          rw [MulAut.conj_apply]; group⟩
    rwa [h] at hz
  intro x hx hx1 k hk
  have hx' : g⁻¹ * x * g ∈ M.D.rootGroup γ := (hmem x).mp hx
  have hx1' : g⁻¹ * x * g ≠ 1 := by
    intro h1
    apply hx1
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]; group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ M.D.rootGroup γ := (hmem y).mp hy
  have hk' : g⁻¹ * k * g ∈ Subgroup.centralizer ({g⁻¹ * x * g} : Set M.K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (g⁻¹ * k * g) * (g⁻¹ * x * g) = g⁻¹ * (k * x) * g := by group
        _ = g⁻¹ * (x * k) * g := by
              rw [Subgroup.mem_centralizer_singleton_iff.mp hk]
        _ = (g⁻¹ * x * g) * (g⁻¹ * k * g) := by group)
  have hkey := hC (g⁻¹ * x * g) hx' hx1' hk'
  rw [Subgroup.mem_centralizer_iff] at hkey
  have hcomm : (g⁻¹ * y * g) * (g⁻¹ * k * g) = (g⁻¹ * k * g) * (g⁻¹ * y * g) :=
    hkey (g⁻¹ * y * g) hy'
  calc y * k = g * ((g⁻¹ * y * g) * (g⁻¹ * k * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * k * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
    _ = k * y := by group

private theorem rckJB4567_trans_of_map_conj {M : LieUniversal}
    {β γ : Fin M.D.rank → ℤ} {g : M.K}
    (h : (M.D.rootGroup γ).map (MulAut.conj g).toMonoidHom = M.D.rootGroup β)
    (htr : ∀ x ∈ M.D.rootGroup γ, x ≠ 1 →
      ∀ y ∈ M.D.rootGroup γ, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (M.D.rootGroup γ : Set M.K), n * x * n⁻¹ = y) :
    ∀ x ∈ M.D.rootGroup β, x ≠ 1 →
      ∀ y ∈ M.D.rootGroup β, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (M.D.rootGroup β : Set M.K), n * x * n⁻¹ = y := by
  have hmem : ∀ z : M.K, z ∈ M.D.rootGroup β ↔ g⁻¹ * z * g ∈ M.D.rootGroup γ := by
    intro z
    have hz : z ∈ (M.D.rootGroup γ).map (MulAut.conj g).toMonoidHom ↔
        g⁻¹ * z * g ∈ M.D.rootGroup γ := by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyz⟩
        change (MulAut.conj g) y = z at hyz
        rw [MulAut.conj_apply] at hyz
        rw [← hyz]
        convert hy using 1
        group
      · intro hz
        exact ⟨g⁻¹ * z * g, hz, by
          change (MulAut.conj g) (g⁻¹ * z * g) = z
          rw [MulAut.conj_apply]; group⟩
    rwa [h] at hz
  intro x hx hx1 y hy hy1
  have hx' : g⁻¹ * x * g ∈ M.D.rootGroup γ := (hmem x).mp hx
  have hy' : g⁻¹ * y * g ∈ M.D.rootGroup γ := (hmem y).mp hy
  have hx1' : g⁻¹ * x * g ≠ 1 := by
    intro h1
    apply hx1
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]; group
  have hy1' : g⁻¹ * y * g ≠ 1 := by
    intro h1
    apply hy1
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h1]; group
  obtain ⟨n, hn, hnx⟩ := htr (g⁻¹ * x * g) hx' hx1' (g⁻¹ * y * g) hy' hy1'
  refine ⟨g * n * g⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    have heq : g⁻¹ * ((g * n * g⁻¹) * z * (g * n * g⁻¹)⁻¹) * g
        = n * (g⁻¹ * z * g) * n⁻¹ := by group
    rw [hmem z, hmem ((g * n * g⁻¹) * z * (g * n * g⁻¹)⁻¹), heq]
    exact Subgroup.mem_normalizer_iff.mp hn (g⁻¹ * z * g)
  · calc (g * n * g⁻¹) * x * (g * n * g⁻¹)⁻¹
        = g * (n * (g⁻¹ * x * g) * n⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hnx]
      _ = y := by group

private theorem rckJB4567_cent_highRoot_adj
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    {i₀ : Fin τ.rank} (hd : RootCentExc.HighRootData τ (highRoot τ) i₀) :
    RCKLemmaHCent ⟨↥(adjointGroup τ K), adjDatum F K⟩ (highRoot τ) := by
  intro x hx hx1 k hk
  change x ∈ rootGroup F K (highRoot τ) at hx
  rw [rootGroup_of_isRoot (isRoot_highRoot τ)] at hx
  have hxT : (x : ModGL τ K) ∈ CFSG.Blueprint.Chevalley.rootSubgroup τ K (highRoot τ) := by
    have h := hx
    rw [← F.subgroupOf_rootSubgroup_eq K ⟨highRoot τ, isRoot_highRoot τ⟩] at h
    rwa [Subgroup.mem_subgroupOf] at h
  have hx1T : (x : ModGL τ K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  change y ∈ rootGroup F K (highRoot τ) at hy
  rw [rootGroup_of_isRoot (isRoot_highRoot τ)] at hy
  have hyT : (y : ModGL τ K) ∈ CFSG.Blueprint.Chevalley.rootSubgroup τ K (highRoot τ) := by
    have h := hy
    rw [← F.subgroupOf_rootSubgroup_eq K ⟨highRoot τ, isRoot_highRoot τ⟩] at h
    rwa [Subgroup.mem_subgroupOf] at h
  have hkT : (k : ModGL τ K) ∈
      Subgroup.centralizer ({(x : ModGL τ K)} : Set (ModGL τ K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)
  have hres := rckHB_cent_highRoot τ K hd hxT hx1T
  have hkres : (k : ModGL τ K) ∈ Subgroup.centralizer
      (CFSG.Blueprint.Chevalley.rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) :=
    hres ⟨k.2, hkT⟩
  rw [Subgroup.mem_centralizer_iff] at hkres
  exact Subtype.ext (hkres (y : ModGL τ K) hyT)

private theorem rckJB4567_trans_highRoot_adj
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    {i₀ : Fin τ.rank} (hd : RootCentExc.HighRootData τ (highRoot τ) i₀) :
    ∀ x ∈ rootGroup F K (highRoot τ), x ≠ 1 →
      ∀ y ∈ rootGroup F K (highRoot τ), y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer
          ((rootGroup F K (highRoot τ) : Set ↥(adjointGroup τ K))),
          n * x * n⁻¹ = y := by
  intro x hx hx1 y hy hy1
  rw [rootGroup_of_isRoot (isRoot_highRoot τ)] at hx hy
  obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := F.mem_rootSubgroup.1 hy
  have hc : c ≠ 0 := by
    intro h0
    exact hx1 (by rw [h0, F.eltElement_zero])
  have hd0 : d ≠ 0 := by
    intro h0
    exact hy1 (by rw [h0, F.eltElement_zero])
  let t : Kˣ := Units.mk0 (d * c⁻¹) (mul_ne_zero hd0 (inv_ne_zero hc))
  refine ⟨torusElement τ K i₀ t, ?_, ?_⟩
  · rw [rootGroup_of_isRoot (isRoot_highRoot τ)]
    have hmap := F.map_conj_torusElement i₀ t ⟨highRoot τ, isRoot_highRoot τ⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hmem : z ∈ F.rootSubgroup K ⟨highRoot τ, isRoot_highRoot τ⟩ ↔
        (MulAut.conj (torusElement τ K i₀ t)) z ∈
          F.rootSubgroup K ⟨highRoot τ, isRoot_highRoot τ⟩ := by
      constructor
      · intro hz
        have h1 : (MulAut.conj (torusElement τ K i₀ t)) z ∈
            (F.rootSubgroup K ⟨highRoot τ, isRoot_highRoot τ⟩).map
              (MulAut.conj (torusElement τ K i₀ t)).toMonoidHom :=
          ⟨z, hz, rfl⟩
        rwa [hmap] at h1
      · intro hz
        have h1 : (MulAut.conj (torusElement τ K i₀ t)) z ∈
            (F.rootSubgroup K ⟨highRoot τ, isRoot_highRoot τ⟩).map
              (MulAut.conj (torusElement τ K i₀ t)).toMonoidHom := by
          rwa [hmap]
        obtain ⟨z', hz', hz'eq⟩ := h1
        have hzz : z' = z := (MulAut.conj _).injective
          (hz'eq.trans (MulAut.conj_apply _ _).symm)
        rwa [← hzz]
    simpa only [MulAut.conj_apply] using hmem
  · have harg : (↑(t ^ ∑ j, τ.cartan i₀ j * (highRoot τ) j) : K) * c = d := by
      have hco : (∑ j, τ.cartan i₀ j * (highRoot τ) j) = 1 := by
        rw [hd.coPair i₀]; simp
      rw [hco, zpow_one, Units.val_mk0, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [F.torusElement_mul_eltElement_mul_inv i₀ t ⟨highRoot τ, isRoot_highRoot τ⟩ c, harg]


theorem rckHB_cent_F4E8
    {t' : StatedLieTag} (ht : t' = .F4 ∨ t' = .E8) {m g : ℕ} (hg : 1 ≤ g)
    {β : Fin (ggU t' m g).D.rank → ℤ} (hβ : GGLongRoot (ggU t' m g).D β) :
    RCKLemmaHCent (ggU t' m g) β := by
  rcases ht with rfl | rfl
  · change RCKLemmaHCent
      (⟨↥(adjointGroup Tag.F4 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)⟩ : LieUniversal) β
    change GGLongRoot ((⟨↥(adjointGroup Tag.F4 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)⟩) : LieUniversal).D β at hβ
    obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hβ
    have hγ₀root : IsRoot Tag.F4 γ₀ := (mem_adjDatum_roots).mp hγ₀
    have hheight : height (τ := Tag.F4) γ₀ = height (τ := Tag.F4) RootCentExc.f4HighRoot :=
      le_antisymm (height_le_height_highRoot hγ₀root)
        (hmax RootCentExc.f4HighRoot (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.F4)))
    have hγ₀eq : γ₀ = RootCentExc.f4HighRoot := rckJB4567_eq_f4HighRoot hγ₀root hheight
    have hγ₀eq' : γ₀ = highRoot Tag.F4 := hγ₀eq
    have hβ' : β = weylAction (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)).isFiniteType
        w (highRoot Tag.F4) := by
      rw [hβeq, hγ₀eq']
    obtain ⟨c, hc⟩ := exists_map_conj_rootGroup
      (D := adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g))
      (adjDatum_isCTGroupDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)) w
    have hgβ : ((adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)).rootGroup
        (highRoot Tag.F4)).map (MulAut.conj c).toMonoidHom =
        (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)).rootGroup β := by
      rw [hc (highRoot Tag.F4) (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.F4)), hβ']
    refine rckJB4567_cent_of_map_conj (M := ⟨↥(adjointGroup Tag.F4 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)⟩) hgβ ?_
    exact rckJB4567_cent_highRoot_adj (F := rootOperatorFamily Tag.F4)
      (K := GaloisField 2 g) RootCentExc.highRootData_F4
  · change RCKLemmaHCent
      (⟨↥(adjointGroup Tag.E8 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)⟩ : LieUniversal) β
    change GGLongRoot ((⟨↥(adjointGroup Tag.E8 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)⟩) : LieUniversal).D β at hβ
    obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hβ
    have hγ₀root : IsRoot Tag.E8 γ₀ := (mem_adjDatum_roots).mp hγ₀
    have hheight : height (τ := Tag.E8) γ₀ = height (τ := Tag.E8) RootCentExc.e8HighRoot :=
      le_antisymm (height_le_height_highRoot hγ₀root)
        (hmax RootCentExc.e8HighRoot (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.E8)))
    have hγ₀eq : γ₀ = RootCentExc.e8HighRoot := rckJB4567_eq_e8HighRoot hγ₀root hheight
    have hγ₀eq' : γ₀ = highRoot Tag.E8 := hγ₀eq
    have hβ' : β = weylAction (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)).isFiniteType
        w (highRoot Tag.E8) := by
      rw [hβeq, hγ₀eq']
    obtain ⟨c, hc⟩ := exists_map_conj_rootGroup
      (D := adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g))
      (adjDatum_isCTGroupDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)) w
    have hgβ : ((adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)).rootGroup
        (highRoot Tag.E8)).map (MulAut.conj c).toMonoidHom =
        (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)).rootGroup β := by
      rw [hc (highRoot Tag.E8) (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.E8)), hβ']
    refine rckJB4567_cent_of_map_conj (M := ⟨↥(adjointGroup Tag.E8 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)⟩) hgβ ?_
    exact rckJB4567_cent_highRoot_adj (F := rootOperatorFamily Tag.E8)
      (K := GaloisField 2 g) RootCentExc.highRootData_E8

theorem rckHB_transitive_F4E8
    {t' : StatedLieTag} (ht : t' = .F4 ∨ t' = .E8) {m g : ℕ} (hg : 1 ≤ g)
    {β : Fin (ggU t' m g).D.rank → ℤ} (hβ : GGLongRoot (ggU t' m g).D β) :
    ∀ x ∈ (ggU t' m g).D.rootGroup β, x ≠ 1 → ∀ y ∈ (ggU t' m g).D.rootGroup β, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((ggU t' m g).D.rootGroup β : Set (ggU t' m g).K), n * x * n⁻¹ = y := by
  rcases ht with rfl | rfl
  ·
    change GGLongRoot ((⟨↥(adjointGroup Tag.F4 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)⟩) : LieUniversal).D β at hβ
    obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hβ
    have hγ₀root : IsRoot Tag.F4 γ₀ := (mem_adjDatum_roots).mp hγ₀
    have hheight : height (τ := Tag.F4) γ₀ = height (τ := Tag.F4) RootCentExc.f4HighRoot :=
      le_antisymm (height_le_height_highRoot hγ₀root)
        (hmax RootCentExc.f4HighRoot (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.F4)))
    have hγ₀eq : γ₀ = RootCentExc.f4HighRoot := rckJB4567_eq_f4HighRoot hγ₀root hheight
    have hγ₀eq' : γ₀ = highRoot Tag.F4 := hγ₀eq
    have hβ' : β = weylAction (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)).isFiniteType
        w (highRoot Tag.F4) := by
      rw [hβeq, hγ₀eq']
    obtain ⟨c, hc⟩ := exists_map_conj_rootGroup
      (D := adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g))
      (adjDatum_isCTGroupDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)) w
    have hgβ : ((adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)).rootGroup
        (highRoot Tag.F4)).map (MulAut.conj c).toMonoidHom =
        (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)).rootGroup β := by
      rw [hc (highRoot Tag.F4) (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.F4)), hβ']
    exact rckJB4567_trans_of_map_conj (M := ⟨↥(adjointGroup Tag.F4 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 g)⟩) hgβ
      (rckJB4567_trans_highRoot_adj (F := rootOperatorFamily Tag.F4)
        (K := GaloisField 2 g) RootCentExc.highRootData_F4)
  ·
    change GGLongRoot ((⟨↥(adjointGroup Tag.E8 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)⟩) : LieUniversal).D β at hβ
    obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hβ
    have hγ₀root : IsRoot Tag.E8 γ₀ := (mem_adjDatum_roots).mp hγ₀
    have hheight : height (τ := Tag.E8) γ₀ = height (τ := Tag.E8) RootCentExc.e8HighRoot :=
      le_antisymm (height_le_height_highRoot hγ₀root)
        (hmax RootCentExc.e8HighRoot (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.E8)))
    have hγ₀eq : γ₀ = RootCentExc.e8HighRoot := rckJB4567_eq_e8HighRoot hγ₀root hheight
    have hγ₀eq' : γ₀ = highRoot Tag.E8 := hγ₀eq
    have hβ' : β = weylAction (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)).isFiniteType
        w (highRoot Tag.E8) := by
      rw [hβeq, hγ₀eq']
    obtain ⟨c, hc⟩ := exists_map_conj_rootGroup
      (D := adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g))
      (adjDatum_isCTGroupDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)) w
    have hgβ : ((adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)).rootGroup
        (highRoot Tag.E8)).map (MulAut.conj c).toMonoidHom =
        (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)).rootGroup β := by
      rw [hc (highRoot Tag.E8) (mem_adjDatum_roots.mpr (isRoot_highRoot Tag.E8)), hβ']
    exact rckJB4567_trans_of_map_conj (M := ⟨↥(adjointGroup Tag.E8 (GaloisField 2 g)),
        adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 g)⟩) hgβ
      (rckJB4567_trans_highRoot_adj (F := rootOperatorFamily Tag.E8)
        (K := GaloisField 2 g) RootCentExc.highRootData_E8)

theorem rck_lemmaH_E8
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .E8 m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .E8 m g).D β) :
    RCKLemmaHTI (ggU .E8 m g) β ∧ RCKLemmaHLevi (ggU .E8 m g) β := by
  exact ⟨rckHB_TI_of_cent (rckHB_cent_F4E8 (Or.inr rfl) hg hβ)
      (rckHB_transitive_F4E8 (Or.inr rfl) hg hβ),
    rckHB_levi_of_cent (rckHB_cent_F4E8 (Or.inr rfl) hg hβ)⟩

theorem rck_lemmaH_F4
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .F4 m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .F4 m g).D β) :
    RCKLemmaHTI (ggU .F4 m g) β ∧ RCKLemmaHLevi (ggU .F4 m g) β := by
  exact ⟨rckHB_TI_of_cent (rckHB_cent_F4E8 (Or.inl rfl) hg hβ)
      (rckHB_transitive_F4E8 (Or.inl rfl) hg hβ),
    rckHB_levi_of_cent (rckHB_cent_F4E8 (Or.inl rfl) hg hβ)⟩

end CFSG.StandardType.RCKC1
