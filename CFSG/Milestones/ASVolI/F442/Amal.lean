module

public import CFSG.Milestones.ASVolI.F442.Count
public import CFSG.Milestones.ASVolI.F442.Quot
public import CFSG.Milestones.ASVolI.F431.L40
public import CFSG.Milestones.ASVolI.F431.RA35Gen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Fusion

theorem burnsideF42g_fusion_of_sylow {E M : Type*} [Group E] [Group M] [Finite E]
    {N S : Subgroup E} (b : ↥N →* M) (hb : Function.Injective b) (hSN : IsSylowTwoOf S N)
    (φ : E → M) (hbφ : ∀ (x : E) (hx : x ∈ S), b ⟨x, hSN.1 hx⟩ = φ x)
    (h35 : ∀ x ∈ S, ∀ y ∈ S, x ≠ 1 → y ≠ 1 → x * x = 1 → y * y = 1 →
      (IsConj x y ↔ IsConj (φ x) (φ y)))
    {s c : E} (hsS : s ∈ S) (hs1 : s ≠ 1) (hs2 : s * s = 1) (hc : c ∈ N) :
    IsConj s c ↔ IsConj (φ s) (b ⟨c, hc⟩) := by
  have hφs : φ s = b ⟨s, hSN.1 hsS⟩ := (hbφ s hsS).symm
  have hbs1 : φ s ≠ 1 := by
    rw [hφs]
    intro h
    apply hs1
    have := hb (h.trans (map_one b).symm)
    exact congrArg Subtype.val this
  by_cases hc1 : c = 1
  · subst hc1
    have hb1 : b ⟨1, hc⟩ = 1 := map_one b
    rw [hb1, isConj_one_left, isConj_one_left]
    exact ⟨fun h => absurd h hs1, fun h => absurd h hbs1⟩
  by_cases hc2 : c * c = 1
  · have hco : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
    obtain ⟨m, hm, hmc⟩ := exists_conj_mem_of_isSylowTwoOf_involution hSN hc hco
    have hc₀1 : m⁻¹ * c * m ≠ 1 := by
      intro h
      apply hc1
      calc c = m * (m⁻¹ * c * m) * m⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hc₀2 : (m⁻¹ * c * m) * (m⁻¹ * c * m) = 1 := by
      calc (m⁻¹ * c * m) * (m⁻¹ * c * m) = m⁻¹ * (c * c) * m := by group
        _ = 1 := by rw [hc2]; group
    have h1 : IsConj s c ↔ IsConj s (m⁻¹ * c * m) :=
      ⟨fun h => h.trans (isConj_iff.mpr ⟨m⁻¹, by group⟩),
        fun h => h.trans (isConj_iff.mpr ⟨m, by group⟩)⟩
    have h2 := h35 s hsS _ hmc hs1 hc₀1 hs2 hc₀2
    have h3 : IsConj (φ (m⁻¹ * c * m)) (b ⟨c, hc⟩) := by
      rw [← hbφ _ hmc]
      refine isConj_iff.mpr ⟨b ⟨m, hm⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1, h2]
    exact ⟨fun h => h.trans h3, fun h => h.trans h3.symm⟩
  · have hl : ¬ IsConj s c := by
      intro h
      obtain ⟨g, hg⟩ := isConj_iff.mp h
      apply hc2
      rw [← hg]
      calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have hr : ¬ IsConj (φ s) (b ⟨c, hc⟩) := by
      intro h
      obtain ⟨g, hg⟩ := isConj_iff.mp h
      apply hc2
      have hsq : b (⟨c, hc⟩ * ⟨c, hc⟩) = b 1 := by
        rw [map_mul, ← hg, map_one, hφs]
        calc g * b ⟨s, hSN.1 hsS⟩ * g⁻¹ * (g * b ⟨s, hSN.1 hsS⟩ * g⁻¹)
            = g * (b ⟨s, hSN.1 hsS⟩ * b ⟨s, hSN.1 hsS⟩) * g⁻¹ := by group
          _ = g * b (⟨s, hSN.1 hsS⟩ * ⟨s, hSN.1 hsS⟩) * g⁻¹ := by rw [map_mul]
          _ = 1 := by
            rw [show (⟨s, hSN.1 hsS⟩ * ⟨s, hSN.1 hsS⟩ : ↥N) = 1 from Subtype.ext hs2, map_one]
            group
      exact congrArg Subtype.val (hb hsq)
    exact ⟨fun h => absurd h hl, fun h => absurd h hr⟩

end Fusion

section Setup

set_option linter.unusedSectionVars false



variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF42g_ctr_conj (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hGp : Gp = ⊤)
    (hκ : κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d) {w₁ w₂ : E}
    (hw₁ : w₁ ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))) (hw₂ : w₂ ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂)))
    (h11 : w₁ ≠ 1) (h12 : w₁ * w₁ = 1) (h21 : w₂ ≠ 1) (h22 : w₂ * w₂ = 1) : IsConj w₁ w₂ := by
  have h27 := as_F_4_27 κ f E Gp M₁ M₂ hyp hGp
  dsimp only at h27
  obtain ⟨-, -, -, h3, -, -⟩ := h27
  obtain ⟨C, -, hCu⟩ := (h3 hκ).2.1
  have e1 := hCu (ConjClasses.mk w₁) ⟨⟨w₁, ConjClasses.mem_carrier_mk, h11, h12⟩,
    ⟨w₁, ConjClasses.mem_carrier_mk, hw₁⟩⟩
  have e2 := hCu (ConjClasses.mk w₂) ⟨⟨w₂, ConjClasses.mem_carrier_mk, h21, h22⟩,
    ⟨w₂, ConjClasses.mem_carrier_mk, hw₂⟩⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mp (e1.trans e2.symm)

theorem burnsideF42g_short (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hGp : Gp = ⊤)
    (hκ : κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d) {z₀ tb : E}
    (hz₀ : z₀ ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))) (hz₀1 : z₀ ≠ 1) (hz₀2 : z₀ * z₀ = 1)
    (ht1 : tb ≠ 1) (ht2 : tb * tb = 1) (htz : ¬ IsConj z₀ tb) :
    IsShortRootInv κ Gp M₁ M₂ tb := by
  have h27 := as_F_4_27 κ f E Gp M₁ M₂ hyp hGp
  dsimp only at h27
  obtain ⟨hm, -, -, h3, -, -⟩ := h27
  obtain ⟨-, -, hls, hliff, -⟩ := h3 hκ
  rcases hls tb ht1 ht2 with hL | hS
  · exfalso
    obtain ⟨g, -, hg⟩ := (hliff tb ht1 ht2).mp hL
    apply htz
    have hg1 : g * tb * g⁻¹ ≠ 1 := by
      intro h
      apply ht1
      calc tb = g⁻¹ * (g * tb * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hg2 : g * tb * g⁻¹ * (g * tb * g⁻¹) = 1 := by
      calc g * tb * g⁻¹ * (g * tb * g⁻¹) = g * (tb * tb) * g⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    exact (burnsideF42g_ctr_conj hyp hGp hκ hz₀ hg hz₀1 hz₀2 hg1 hg2).trans
      (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  · exact ⟨f, hyp.toHypF_4_4g.chart, hm, hS⟩

theorem burnsideF42g_setup (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hGp : Gp = ⊤)
    (hκ : κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d)
    (h35 : ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)))
    {z₀ tb : E} (hz₀ : z₀ ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))) (hz₀1 : z₀ ≠ 1) (hz₀2 : z₀ * z₀ = 1)
    (htS : tb ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (ht1 : tb ≠ 1) (ht2 : tb * tb = 1) (htM : tb ∈ M₂)
    (hCt : Subgroup.centralizer ({tb} : Set E) ≤ M₂)
    (hSylt : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({tb} : Set E))
      (Gp ⊓ Subgroup.centralizer ({tb} : Set E))) :
    (∀ (c : E) (hc : c ∈ Subgroup.centralizer ({tb} : Set E)), IsConj z₀ c →
      burnsideF42g_FixIn (Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨tb, htM⟩} : Set M))
        ((burnsideF4d_bTwo β ε).comp (Subgroup.inclusion hCt)).range
        (burnsideF4d_bTwo β ε ⟨c, hCt hc⟩)) ∧
    (∀ w ∈ Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨tb, htM⟩} : Set M),
      (∃ n : ℕ, w ^ (2 ^ n) = 1) →
      ∃ k ∈ Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨tb, htM⟩} : Set M),
        k⁻¹ * w * k ∈ ((burnsideF4d_bTwo β ε).comp (Subgroup.inclusion hCt)).range) := by
  classical
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hGp
  set b₁ := burnsideF4d_bOne β ε with hb₁def
  set b₂ := burnsideF4d_bTwo β ε with hb₂def
  have hb₁ : Function.Injective b₁ := burnsideF4j_bOne_injective hyp
  have hb₂ : Function.Injective b₂ := burnsideF4j_bTwo_injective hyp
  have hag : ∀ x (h1 : x ∈ M₁) (h2 : x ∈ M₂), b₁ ⟨x, h1⟩ = b₂ ⟨x, h2⟩ :=
    fun x h1 h2 => burnsideF4j_bOne_eq_bTwo β ε x h1 h2
  set φ := amalgamMap b₁ b₂ with hφ
  have hφ₁ : ∀ x (hx : x ∈ M₁), φ x = b₁ ⟨x, hx⟩ := fun x hx => amalgamMap_of_mem₁ b₁ b₂ hx
  have hφ₂ : ∀ x (hx : x ∈ M₂), φ x = b₂ ⟨x, hx⟩ :=
    fun x hx => amalgamMap_of_mem₂ b₁ b₂ hag hx
  set S := pCoreOf 2 ((⊤ : Subgroup E) ⊓ (M₁ ⊓ M₂)) with hSdef
  have hSeq : S = pCoreOf 2 (M₁ ⊓ M₂) := by rw [hSdef, top_inf_eq]
  have hSB : S ≤ ⊤ ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hS12 : S ≤ M₁ ⊓ M₂ := fun s hs => (hSB hs).2
  have hS1 : S ≤ M₁ := fun s hs => (hS12 hs).1
  have hS2 : S ≤ M₂ := fun s hs => (hS12 hs).2
  have hSp : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨hSyl, -⟩ := burnsideF4j_sylow_data hyp.amalgam
  have hSM₁ : IsSylowTwoOf S M₁ := F7.isSylowTwoOf_mono_right hSyl hS1 le_top
  have hSM₂ : IsSylowTwoOf S M₂ := F7.isSylowTwoOf_mono_right hSyl hS2 le_top
  have h35' : ∀ x ∈ S, ∀ y ∈ S, x ≠ 1 → y ≠ 1 → x * x = 1 → y * y = 1 →
      (IsConj x y ↔ IsConj (φ x) (φ y)) := by
    intro x hx y hy hx1 hy1 hx2 hy2
    have h := h35 ⟨x, hS12 hx⟩ ⟨y, hS12 hy⟩ hx hy (fun h => hx1 (congrArg Subtype.val h))
      (fun h => hy1 (congrArg Subtype.val h)) (Subtype.ext hx2) (Subtype.ext hy2)
    rw [burnsideF4j_bM_eq_bOne, burnsideF4j_bM_eq_bOne] at h
    rw [hφ₁ x (hS1 hx), hφ₁ y (hS1 hy), ← h]
    constructor
    · intro hc
      obtain ⟨g, hg⟩ := isConj_iff.mp hc
      exact ⟨g, Subgroup.mem_top g, hg⟩
    · rintro ⟨g, -, hg⟩
      exact isConj_iff.mpr ⟨g, hg⟩
  have hbφ₁ : ∀ (x : E) (hx : x ∈ S), b₁ ⟨x, hSM₁.1 hx⟩ = φ x := fun x hx => (hφ₁ x _).symm
  have hbφ₂ : ∀ (x : E) (hx : x ∈ S), b₂ ⟨x, hSM₂.1 hx⟩ = φ x := fun x hx => (hφ₂ x _).symm
  obtain ⟨xb, hxZ, hxz, hx1, hx2⟩ := burnsideF4r_zbar hyp hκ.1
  have hxS : (xb : E) ∈ S := hxZ.1
  have hxb1 : (xb : E) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxb2 : (xb : E) * xb = 1 := congrArg Subtype.val hx2
  have hφx : φ xb = z := by
    rw [hφ₁ _ xb.2.1, ← hxz, burnsideF4j_bM_eq_bOne]
  have hxO : (xb : E) ∈ ctr (oPPrime 2 M₁) := by
    have hz := hyp.z_mem.1 hκ.1
    rw [burnsideF4j_Z1_eq hyp] at hz
    obtain ⟨x', hx'1, hx'Z, hx'z⟩ := mem_subImg.mp hz
    have e : x' = (xb : E) := by
      have : b₁ ⟨x', hx'1⟩ = b₁ ⟨xb, xb.2.1⟩ := by rw [hx'z, ← hxz, burnsideF4j_bM_eq_bOne]
      exact congrArg Subtype.val (hb₁ this)
    rw [← e]
    rwa [top_inf_eq] at hx'Z
  have h27 := as_F_4_27 κ f E ⊤ M₁ M₂ hyp.amalgam rfl
  dsimp only at h27
  obtain ⟨-, -, -, -, h4, -⟩ := h27
  have hCx : Subgroup.centralizer ({(xb : E)} : Set E) ≤ M₁ :=
    ((h4 hκ.1).1 xb hxO hxb1).2.2.1
  have hz₀x : IsConj z₀ (xb : E) := by
    refine burnsideF42g_ctr_conj hyp.amalgam rfl hκ hz₀ ?_ hz₀1 hz₀2 hxb1 hxb2
    rw [← hSeq]
    exact hxZ
  set t := b₂ ⟨tb, htM⟩ with htdef
  have hφt : φ tb = t := hφ₂ tb htM
  have hSinM : ChF.IsSylowOf 2 (SinM ⊤ β ε) ⊤ := by
    apply burnsideF4j_F_4_33_odd hyp (by rw [Subgroup.index_top]; exact odd_one)
    rw [burnsideF4d_SinM_eq]
    have hP : IsPGroup 2 (subImg b₁ S) := by
      unfold subImg
      exact (hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hS1).symm).map b₁
    have hSylR : IsSylowTwoOf (subImg b₁ S) b₁.range := by
      refine F7.isSylowTwoOf_of_relIndex (by unfold subImg; exact Subgroup.map_le_range b₁ _) hP ?_
      rw [MonoidHom.range_eq_map]
      unfold subImg
      rw [Subgroup.relIndex_map_map_of_injective _ _ hb₁, Subgroup.relIndex_top_right]
      exact hSM₁.2.2
    have hle : subImg b₁ S ≤ MiOne β ε ⊓ MiTwo β ε := by
      rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj]
      intro y hy
      obtain ⟨s, hs, hsS, rfl⟩ := mem_subImg.mp hy
      exact mem_subImg_of_mem b₁ hs (hS12 hsS)
    have hMi : MiOne β ε ⊓ MiTwo β ε ≤ b₁.range := by
      refine inf_le_left.trans ?_
      rw [burnsideF4d_MiOne_eq, subImg_self]
    exact F7.isSylowTwoOf_mono_right hSylR hle hMi
  have hbt : bM β ε ⟨tb, hS12 htS⟩ = t := by
    rw [burnsideF4j_bM_eq_bOne, hag]
  have h40 := burnsideF4m_F_4_40_inst hyp hSinM h35 ⟨tb, hS12 htS⟩ htS
    (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext ht2) hSylt
  rw [hbt] at h40
  set ψ₂ := b₂.comp (Subgroup.inclusion hCt) with hψ₂def
  have hψ₂ : Function.Injective ψ₂ := hb₂.comp (Subgroup.inclusion_injective hCt)
  have hconj2 : ∀ w ∈ Subgroup.centralizer ({t} : Set M), (∃ n : ℕ, w ^ (2 ^ n) = 1) →
      ∃ k ∈ Subgroup.centralizer ({t} : Set M), k⁻¹ * w * k ∈ ψ₂.range := by
    rintro w hw ⟨n, hn⟩
    have hp : IsPGroup 2 (Subgroup.zpowers w) :=
      CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow (k := n) hn
    obtain ⟨k, hk, hle⟩ := F7.isSylowTwoOf_exists_conj_le h40 (Subgroup.zpowers_le.mpr hw) hp
    refine ⟨k, hk, ?_⟩
    obtain ⟨hwS, hwC⟩ := mem_conjSub.mp (hle (Subgroup.mem_zpowers w))
    rw [burnsideF4d_SinM_eq] at hwS
    obtain ⟨s, hs1, hsS, hbs⟩ := mem_subImg.mp hwS
    have hst : s * tb = tb * s := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hwC
      rw [← hbs, htdef, ← hag tb (hS1 htS) htM, ← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hb₁ h1)
    have hsC : s ∈ Subgroup.centralizer ({tb} : Set E) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hst
    refine ⟨⟨s, hsC⟩, ?_⟩
    rw [← hbs, hψ₂def, MonoidHom.comp_apply]
    exact (hag s hs1 (hCt hsC)).symm
  refine ⟨fun c hc hcz => ?_, hconj2⟩
  set ψ₁ := b₁.comp (Subgroup.inclusion hCx) with hψ₁def
  have hψ₁ : Function.Injective ψ₁ := hb₁.comp (Subgroup.inclusion_injective hCx)
  have hr₁ : ψ₁.range = Subgroup.centralizer ({z} : Set M) := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hφx, hφ₁ _ xb.2.1, hψ₁def,
        MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
    · intro hy
      have hyM := hyp.hb hy
      rw [burnsideF4d_MiOne_eq, subImg_self] at hyM
      obtain ⟨m, rfl⟩ := hyM
      have hmx : (m : E) * xb = xb * m := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hy
        rw [← hφx, hφ₁ _ xb.2.1, ← map_mul, ← map_mul] at h1
        exact congrArg Subtype.val (hb₁ h1)
      exact ⟨⟨m, Subgroup.mem_centralizer_singleton_iff.mpr hmx⟩, rfl⟩
  have hX : ψ₂.range ≤ Subgroup.centralizer ({t} : Set M) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hψ₂def, MonoidHom.comp_apply, htdef,
      ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have hf₁ : ∀ c : Subgroup.centralizer ({(xb : E)} : Set E), IsConj tb (c : E) ↔ IsConj t (ψ₁ c) := by
    intro c
    rw [← hφt]
    exact burnsideF42g_fusion_of_sylow b₁ hb₁ hSM₁ φ hbφ₁ h35' htS ht1 ht2 (hCx c.2)
  have hf₂ : ∀ c : Subgroup.centralizer ({tb} : Set E), IsConj (xb : E) (c : E) ↔
      IsConj z (ψ₂ c) := by
    intro c
    rw [← hφx]
    exact burnsideF42g_fusion_of_sylow b₂ hb₂ hSM₂ φ hbφ₂ h35' hxS hxb1 hxb2 (hCt c.2)
  have h40' : ∀ y ∈ Subgroup.centralizer ({t} : Set M), IsConj z y →
      ∃ k ∈ Subgroup.centralizer ({t} : Set M), k⁻¹ * y * k ∈ ψ₂.range := by
    intro y hy hyz
    refine hconj2 y hy ⟨1, ?_⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hyz
    rw [pow_one, pow_two, ← hg]
    have hz2 : z * z = 1 := hyp.z_inv.2
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hyX : b₂ ⟨c, hCt hc⟩ ∈ ψ₂.range := ⟨⟨c, hc⟩, rfl⟩
  have hyz : IsConj z (b₂ ⟨c, hCt hc⟩) := (hf₂ ⟨c, hc⟩).mp (hz₀x.symm.trans hcz)
  intro h hh hhy
  exact burnsideF42g_lemmaA ψ₁ hψ₁ hr₁ ψ₂ hψ₂ hX hf₁ hf₂ h40' hyX hyz hh hhy

theorem burnsideF42g_HX (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) {tb : E} (ht2 : tb * tb = 1)
    (htM : tb ∈ M₂) (hCt : Subgroup.centralizer ({tb} : Set E) ≤ M₂) :
    burnsideF4d_bTwo β ε ⟨tb, htM⟩ ∈
        Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨tb, htM⟩} : Set M) ∧
      burnsideF4d_bTwo β ε ⟨tb, htM⟩ ∈
        ((burnsideF4d_bTwo β ε).comp (Subgroup.inclusion hCt)).range ∧
      ((burnsideF4d_bTwo β ε).comp (Subgroup.inclusion hCt)).range ≤
        Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨tb, htM⟩} : Set M) ∧
      (∀ h ∈ Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨tb, htM⟩} : Set M),
        h * burnsideF4d_bTwo β ε ⟨tb, htM⟩ = burnsideF4d_bTwo β ε ⟨tb, htM⟩ * h) ∧
      burnsideF4d_bTwo β ε ⟨tb, htM⟩ * burnsideF4d_bTwo β ε ⟨tb, htM⟩ = 1 ∧
      ((burnsideF4d_bTwo β ε).comp (Subgroup.inclusion hCt)).range ≤ MiTwo β ε := by
  have htC : tb ∈ Subgroup.centralizer ({tb} : Set E) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ⟨⟨tb, htC⟩, rfl⟩, ?_,
    fun h hh => Subgroup.mem_centralizer_singleton_iff.mp hh, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  · rw [← map_mul, ← map_one (burnsideF4d_bTwo β ε)]
    congr 1
    exact Subtype.ext ht2
  · rintro _ ⟨c, rfl⟩
    rw [burnsideF4d_MiTwo_eq, subImg_self]
    exact ⟨_, rfl⟩

theorem burnsideF42g_A42_of_lemmaB (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hGp : Gp = ⊤)
    (hκ : κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d)
    (h35 : ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)))
    {z₀ tb : E} (hz₀ : z₀ ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))) (hz₀1 : z₀ ≠ 1) (hz₀2 : z₀ * z₀ = 1)
    (htQ : tb ∈ pCoreOf 2 (Gp ⊓ M₂)) (htS : tb ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (ht1 : tb ≠ 1)
    (ht2 : tb * tb = 1) (htz : ¬ IsConj z₀ tb)
    (hCt : Subgroup.centralizer ({tb} : Set E) ≤ M₂)
    (hSylt : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({tb} : Set E))
      (Gp ⊓ Subgroup.centralizer ({tb} : Set E)))
    (hGc : ∀ c ∈ Subgroup.centralizer ({tb} : Set E), (c * c = 1 ∨ c * c = tb) → c ≠ 1 →
      c ≠ tb → IsConj z₀ c ∨ IsConj z₀ (c * tb))
    {a b : E} (haC : a ∈ Subgroup.centralizer ({tb} : Set E))
    (hbC : b ∈ Subgroup.centralizer ({tb} : Set E)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (haz : IsConj z₀ a) (hbz : IsConj z₀ b)
    (hab : ∀ x ∈ Subgroup.centralizer ({tb} : Set E), x * a * x⁻¹ ≠ b ∧ x * a * x⁻¹ ≠ b * tb) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  haveI := hyp.finite_M
  have htC : tb ∈ Subgroup.centralizer ({tb} : Set E) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htM : tb ∈ M₂ := hCt htC
  refine ⟨⟨tb, htM⟩, htQ, burnsideF42g_short hyp.amalgam hGp hκ hz₀ hz₀1 hz₀2 ht1 ht2 htz, ?_⟩
  obtain ⟨hfix, hconj2⟩ :=
    burnsideF42g_setup hyp hGp hκ h35 hz₀ hz₀1 hz₀2 htS ht1 ht2 htM hCt hSylt
  obtain ⟨htH, htX, hXH, hcen, ht2', hXM⟩ := burnsideF42g_HX hyp ht2 htM hCt
  set b₂ := burnsideF4d_bTwo β ε with hb₂def
  have hb₂ : Function.Injective b₂ := burnsideF4j_bTwo_injective hyp
  set t := b₂ ⟨tb, htM⟩ with htdef
  set X := (b₂.comp (Subgroup.inclusion hCt)).range with hXdef
  have hsq : ∀ (c : E) (hc : c ∈ M₂), c * c = 1 → b₂ ⟨c, hc⟩ * b₂ ⟨c, hc⟩ = 1 := by
    intro c hc h
    rw [← map_mul, ← map_one b₂]
    congr 1
    exact Subtype.ext h
  have hmulT : ∀ (c : E) (hc : c ∈ M₂), b₂ ⟨c, hc⟩ * t = b₂ ⟨c * tb, M₂.mul_mem hc htM⟩ := by
    intro c hc
    rw [htdef, ← map_mul]
    rfl
  show Subgroup.centralizer ({t} : Set M) ≤ MiTwo β ε
  refine le_trans ?_ hXM
  refine burnsideF42g_le_of_fix1_mod htH htX hXH hcen ht2' ⟨⟨a, haC⟩, rfl⟩ ⟨⟨b, hbC⟩, rfl⟩
    (hsq a (hCt haC) ha2) (hsq b (hCt hbC) hb2) (hfix a haC haz) (hfix b hbC hbz) ?_ ?_
  · rintro _ ⟨x, rfl⟩
    simp only [MonoidHom.comp_apply]
    have e1 : b₂ (Subgroup.inclusion hCt x) * b₂ (Subgroup.inclusion hCt ⟨a, haC⟩) *
        (b₂ (Subgroup.inclusion hCt x))⁻¹ =
        b₂ ⟨(x : E) * a * (x : E)⁻¹, M₂.mul_mem (M₂.mul_mem (hCt x.2) (hCt haC))
          (M₂.inv_mem (hCt x.2))⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e2 : b₂ (Subgroup.inclusion hCt ⟨b, hbC⟩) * t = b₂ ⟨b * tb, M₂.mul_mem (hCt hbC) htM⟩ :=
      hmulT b (hCt hbC)
    rw [e1, e2]
    constructor
    · intro h
      exact (hab x x.2).1 (congrArg Subtype.val (hb₂ h))
    · intro h
      exact (hab x x.2).2 (congrArg Subtype.val (hb₂ h))
  · intro w hw hw2 hw1 hwt
    have hw4 : w ^ (2 ^ 2) = 1 := by
      rcases hw2 with h | h
      · rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two, h, one_mul]
      · rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two, h, ht2']
    obtain ⟨k, hk, ⟨c, hc⟩⟩ := hconj2 w hw ⟨2, hw4⟩
    refine ⟨k, hk, ⟨c, hc⟩, ?_⟩
    have hkt : k * t = t * k := hcen k hk
    rw [← hc]
    simp only [MonoidHom.comp_apply]
    have hcM : (c : E) ∈ M₂ := hCt c.2
    have hci : b₂ ⟨c, hcM⟩ = k⁻¹ * w * k := hc
    have hcsq : b₂ (⟨c, hcM⟩ * ⟨c, hcM⟩) = k⁻¹ * (w * w) * k := by
      rw [map_mul, hci]; group
    have hc2 : (c : E) * c = 1 ∨ (c : E) * c = tb := by
      rcases hw2 with h | h
      · left
        rw [h, show k⁻¹ * 1 * k = 1 by group, ← map_one b₂] at hcsq
        exact congrArg Subtype.val (hb₂ hcsq)
      · right
        rw [h, show k⁻¹ * t * k = t by rw [mul_assoc, ← hkt]; group, htdef] at hcsq
        exact congrArg Subtype.val (hb₂ hcsq)
    have hc1 : (c : E) ≠ 1 := by
      intro h
      apply hw1
      have : b₂ ⟨c, hcM⟩ = 1 := by
        rw [← map_one b₂]
        congr 1
        exact Subtype.ext h
      rw [hci] at this
      calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hct : (c : E) ≠ tb := by
      intro h
      apply hwt
      have : b₂ ⟨c, hcM⟩ = t := by
        rw [htdef]
        congr 1
        exact Subtype.ext h
      rw [hci] at this
      calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
        _ = k * t * k⁻¹ := by rw [this]
        _ = t := by rw [hkt]; group
    show burnsideF42g_FixIn _ _ (b₂ ⟨c, hcM⟩)
    rcases hGc c c.2 hc2 hc1 hct with hz | hz
    · exact hfix c c.2 hz
    · have hcC : (c : E) * tb ∈ Subgroup.centralizer ({tb} : Set E) :=
        Subgroup.mul_mem _ c.2 htC
      have h1 := hfix _ hcC hz
      rw [← hmulT c hcM] at h1
      exact burnsideF42g_fixIn_of_mul htX hcen h1

theorem burnsideF42g_A42_of_lemmaU (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hGp : Gp = ⊤)
    (hκ : κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d)
    (h35 : ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)))
    {z₀ tb : E} (hz₀ : z₀ ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))) (hz₀1 : z₀ ≠ 1) (hz₀2 : z₀ * z₀ = 1)
    (htQ : tb ∈ pCoreOf 2 (Gp ⊓ M₂)) (htS : tb ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (ht1 : tb ≠ 1)
    (ht2 : tb * tb = 1) (htz : ¬ IsConj z₀ tb)
    (hCt : Subgroup.centralizer ({tb} : Set E) ≤ M₂)
    (hSylt : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({tb} : Set E))
      (Gp ⊓ Subgroup.centralizer ({tb} : Set E)))
    {u v₁ v₂ : E} (huC : u ∈ Subgroup.centralizer ({tb} : Set E)) (hu2 : u * u = 1)
    (huz : IsConj z₀ u)
    (huc : ∀ x ∈ Subgroup.centralizer ({tb} : Set E), x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * tb)
    (hv₁C : v₁ ∈ Subgroup.centralizer ({tb} : Set E)) (hv₁2 : v₁ * v₁ = 1) (hv₁z : IsConj z₀ v₁)
    (h₁ : v₁ ≠ u ∧ v₁ ≠ u * tb)
    (hv₂C : v₂ ∈ Subgroup.centralizer ({tb} : Set E)) (hv₂2 : v₂ * v₂ = 1) (hv₂z : IsConj z₀ v₂)
    (h₂ : v₂ ≠ u ∧ v₂ ≠ u * tb)
    (h₁₂ : IsConj z₀ (v₁ * v₂) ∨ IsConj z₀ (v₁ * v₂ * tb)) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  haveI := hyp.finite_M
  have htC : tb ∈ Subgroup.centralizer ({tb} : Set E) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htM : tb ∈ M₂ := hCt htC
  refine ⟨⟨tb, htM⟩, htQ, burnsideF42g_short hyp.amalgam hGp hκ hz₀ hz₀1 hz₀2 ht1 ht2 htz, ?_⟩
  obtain ⟨hfix, -⟩ :=
    burnsideF42g_setup hyp hGp hκ h35 hz₀ hz₀1 hz₀2 htS ht1 ht2 htM hCt hSylt
  obtain ⟨htH, htX, hXH, hcen, ht2', hXM⟩ := burnsideF42g_HX hyp ht2 htM hCt
  set b₂ := burnsideF4d_bTwo β ε with hb₂def
  have hb₂ : Function.Injective b₂ := burnsideF4j_bTwo_injective hyp
  set t := b₂ ⟨tb, htM⟩ with htdef
  have hsq : ∀ (c : E) (hc : c ∈ M₂), c * c = 1 → b₂ ⟨c, hc⟩ * b₂ ⟨c, hc⟩ = 1 := by
    intro c hc h
    rw [← map_mul, ← map_one b₂]
    congr 1
    exact Subtype.ext h
  have hmulT : ∀ (c : E) (hc : c ∈ M₂), b₂ ⟨c, hc⟩ * t = b₂ ⟨c * tb, M₂.mul_mem hc htM⟩ := by
    intro c hc
    rw [htdef, ← map_mul]
    rfl
  have hne : ∀ (v : E) (hv : v ∈ Subgroup.centralizer ({tb} : Set E)), v ≠ u ∧ v ≠ u * tb →
      b₂ ⟨v, hCt hv⟩ ≠ b₂ ⟨u, hCt huC⟩ ∧ b₂ ⟨v, hCt hv⟩ ≠ b₂ ⟨u, hCt huC⟩ * t := by
    intro v hv h
    rw [hmulT u (hCt huC)]
    exact ⟨fun e => h.1 (congrArg Subtype.val (hb₂ e)),
      fun e => h.2 (congrArg Subtype.val (hb₂ e))⟩
  have hf₁₂ : burnsideF42g_FixIn (Subgroup.centralizer ({t} : Set M))
      (b₂.comp (Subgroup.inclusion hCt)).range (b₂ ⟨v₁, hCt hv₁C⟩ * b₂ ⟨v₂, hCt hv₂C⟩) := by
    have hvC : v₁ * v₂ ∈ Subgroup.centralizer ({tb} : Set E) := Subgroup.mul_mem _ hv₁C hv₂C
    have e : b₂ ⟨v₁, hCt hv₁C⟩ * b₂ ⟨v₂, hCt hv₂C⟩ = b₂ ⟨v₁ * v₂, hCt hvC⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    rcases h₁₂ with hz | hz
    · exact hfix _ hvC hz
    · have hvtC : v₁ * v₂ * tb ∈ Subgroup.centralizer ({tb} : Set E) := Subgroup.mul_mem _ hvC htC
      have h1 := hfix _ hvtC hz
      rw [← hmulT _ (hCt hvC)] at h1
      exact burnsideF42g_fixIn_of_mul htX hcen h1
  show Subgroup.centralizer ({t} : Set M) ≤ MiTwo β ε
  refine le_trans ?_ hXM
  refine burnsideF42g_le_of_fix1_central_mod htH htX hXH hcen ht2' ⟨⟨u, huC⟩, rfl⟩
    (hsq u (hCt huC) hu2) ?_ (hfix u huC huz) ⟨⟨v₁, hv₁C⟩, rfl⟩ (hsq v₁ (hCt hv₁C) hv₁2)
    (hfix v₁ hv₁C hv₁z) (hne v₁ hv₁C h₁) ⟨⟨v₂, hv₂C⟩, rfl⟩ (hsq v₂ (hCt hv₂C) hv₂2)
    (hfix v₂ hv₂C hv₂z) (hne v₂ hv₂C h₂) hf₁₂
  rintro _ ⟨x, rfl⟩
  simp only [MonoidHom.comp_apply]
  have e1 : b₂ (Subgroup.inclusion hCt x) * b₂ (Subgroup.inclusion hCt ⟨u, huC⟩) *
      (b₂ (Subgroup.inclusion hCt x))⁻¹ =
      b₂ ⟨(x : E) * u * (x : E)⁻¹, M₂.mul_mem (M₂.mul_mem (hCt x.2) (hCt huC))
        (M₂.inv_mem (hCt x.2))⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have e2 : b₂ (Subgroup.inclusion hCt ⟨u, huC⟩) * t = b₂ ⟨u * tb, M₂.mul_mem (hCt huC) htM⟩ :=
    hmulT u (hCt huC)
  have e3 : b₂ (Subgroup.inclusion hCt ⟨u, huC⟩) = b₂ ⟨u, hCt huC⟩ := rfl
  rw [e1, e2, e3]
  rcases huc x x.2 with h | h
  · left
    congr 1
    exact Subtype.ext h
  · right
    congr 1
    exact Subtype.ext h

end Setup

end CFSG.ASVolI
