module

public import CFSG.Quasithin.Vol2.Ch11SecA15S5
public import CFSG.Quasithin.Vol2.Ch11SecA15CT
public import CFSG.Quasithin.Vol2.Ch11SecA15GO5
public import CFSG.Quasithin.Vol2.Ch11SecA15TI

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem V1_eq_inf (hF : Facts15) (hFc : Facts15c) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    V₁ = fsuV T I ⊓ Subgroup.centralizer (ROf T L V₁ : Set G) :=
  le_antisymm (le_inf (IsVi.le_fsuV hU)
      (Subgroup.le_centralizer_iff.mp (ROf_le_centralizer_V1' hFc hF11 hG2 h1102 h hU hk)))
    fun x ⟨hxV, hxC⟩ => mem_V1_of_fixed hF h1102 h hU hxV fun r hr => by
      rw [Subgroup.mem_centralizer_iff.mp hxC r hr, mul_inv_cancel_right]

theorem normalizer_le_of_centralizer (h331 : Stmt3_3_1) (h : Hyp11 G T L I n)
    {Z C : Subgroup G} (hYZ : Subgroup.normalizer (ROf T L V₁ : Set G) ≤
      Subgroup.normalizer (Z : Set G)) (hT : T ≤ Subgroup.centralizer (Z : Set G))
    (hCZ : C ≤ Z) (hNC : Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  have hT2 := h.fsu.sylow
  set K := Subgroup.centralizer (Z : Set G) with hK
  have hTK : IsSylowTwoOf T K := ⟨hT, hT2.1, fun h2 => hT2.2
    (h2.trans (by rw [← Subgroup.relIndex]; exact Subgroup.relIndex_dvd_index_of_le hT))⟩
  have hyZ := hYZ hy
  have hle : T.map (MulAut.conj y).toMonoidHom ≤ K := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : y⁻¹ * z * y ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyZ) z).mp hz
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hT ht) _ hz'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc z * (y * t * y⁻¹) = y * ((y⁻¹ * z * y) * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * z * y)) * y⁻¹ := by rw [h1]
      _ = y * t * y⁻¹ * z := by group
  have hTyK : IsSylowTwoOf (T.map (MulAut.conj y).toMonoidHom) K := by
    refine ⟨hle, hT2.1.map _, fun h2 => hT2.2 ?_⟩
    have h3 : (T.map (MulAut.conj y).toMonoidHom).index = T.index :=
      Subgroup.index_map_equiv T (MulAut.conj y)
    rw [← h3]
    exact h2.trans (by rw [← Subgroup.relIndex]; exact Subgroup.relIndex_dvd_index_of_le hle)
  obtain ⟨c, hcK, hc⟩ := hTK.exists_conj hTyK
  have hcy : c⁻¹ * y ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have e1 : g ∈ T ↔ y * g * y⁻¹ ∈ T.map (MulAut.conj y).toMonoidHom := by
      rw [OnanData.mem_map_conj_iff]
      simp [mul_assoc]
    rw [e1, hc, OnanData.mem_map_conj_iff]
    simp [mul_assoc]
  have hcL : c ∈ Subgroup.normalizer (L : Set G) :=
    hNC (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun x hx => hCZ hx) hcK))
  have : y = c * (c⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ hcL (normalizer_T_le h331 h hcy)

theorem inf_centralizer_eq_bot (h331 : Stmt3_3_1) (h4213 : TmpL6_4_2_13) (h1104 : Stmt11_0_4)
    (hF : Facts15) (hFc : Facts15c) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hB : IsSL3Block L ∨ IsSp4Block L)
    (hNot : ¬ Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hC
  have hk := kind_of_block hG2 h1102 h hB
  have hS := IsSL3Block_or_IsSp4Block.isShort2 hB
  have hVM := fsuV_eq_VM h1102 h hS
  have hMV := normalizer_le_normalizer_fsuV h1102 h hS
  have hZ₁R : omegaOneCenterOf (ROf T L V₁) ≤ ROf T L V₁ :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.1
  have hZC2 : IsPGroup 2 ↥(omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G)) :=
    isPGroup_ROf.to_le (inf_le_left.trans hZ₁R)
  have hZCne := zC_ne_bot (V₁ := V₁) h hC
  have hTR : T ≤ Subgroup.normalizer (ROf T L V₁ : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hYZ := normalizer_le_normalizer_omegaOneCenterOf (ROf T L V₁)
  have hNC : ∀ y ∈ Subgroup.normalizer (ROf T L V₁ : Set G), y ∈ Subgroup.normalizer (L : Set G) →
      y ∈ Subgroup.normalizer ((omegaOneCenterOf (ROf T L V₁) ⊓
        Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun y hy hyL =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hYZ hy, mem_normalizer_centralizer hyL⟩
  have hLTZC : L ⊔ T ≤ Subgroup.normalizer ((omegaOneCenterOf (ROf T L V₁) ⊓
      Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine sup_le ((Subgroup.le_centralizer_iff.mp inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)) fun t ht => hNC t (hTR ht) (h.normal ht)
  have hNZC := normalizer_le_of_isPGroup h331 h hZC2 hZCne hLTZC
  obtain ⟨d₀, hd₀L, hd₀V, hd₀V₁, hgen, ⟨m, hm, hdm⟩, htr⟩ := torus_data hFc hG2 h1102 h hU hk
  have hd₀R := lOf_inf_le_normalizer_ROf hFc hG2 h1102 h hU hk ⟨hd₀L, hd₀V₁⟩
  have hcz : ∀ g ∈ L, ∀ hgV : g ∈ Subgroup.normalizer (fsuV T I : Set G),
      conjV (fsuV T I) g hgV ∈
        perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I))) →
      g ∈ Subgroup.centralizer (omegaOneCenterOf (ROf T L V₁) : Set G) :=
    fun g hgL hgV hg => mem_centralizer_Z1 hF hFc hF11 hG2 h1102 h1103 h hU hB hgL
      (centralizes_V1_of_mem hF11 h1102 h hU hgL hgV hg)
  have hV1n : ∀ y ∈ Subgroup.normalizer (ROf T L V₁ : Set G),
      y ∈ Subgroup.normalizer (fsuV T I : Set G) → y ∈ Subgroup.normalizer (V₁ : Set G) := by
    intro y hy hyV
    rw [V1_eq_inf hF hFc hF11 hG2 h1102 h hU hk]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hyV, mem_normalizer_centralizer hy⟩
  have hVZ := V1_le_Z1 hFc hF11 hG2 h1102 h hU hk
  obtain ⟨v₀, hv₀, w₀, hw₀, hv₀C, hw₀C, hvw₀⟩ := three_points h hU
  have hnotC : ∀ x ∈ V₁, x ∉ Subgroup.centralizer (L : Set G) →
      x ∉ omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G) :=
    fun x _ hx h' => hx h'.2
  have D : OnanData (omegaOneCenterOf (ROf T L V₁)) (Subgroup.normalizer (ROf T L V₁ : Set G)) T
      V₁ (omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G)) d₀ :=
    { exp2 := exp2_omegaOneCenterOf _
      YZ := hYZ
      TY := hTR
      T2 := h.fsu.sylow.1
      Todd := fun h2 => h.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTR))
      VZ := hVZ
      CZ := inf_le_left
      ZVC := Z1_le_sup hF hFc hF11 hG2 h1102 h1103 h hU hB
      Cne := hZCne
      dY := hd₀R
      dV := hd₀V₁
      dC := fun c hc => Subgroup.mem_centralizer_iff.mp hc.2 d₀ hd₀L
      odd := ⟨m, hm, fun z hz => by
        have h1 := hcz _ (L.pow_mem hd₀L m) (Subgroup.pow_mem _ hd₀V m)
          (by rw [conjV_pow]; exact hdm)
        exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm⟩
      trans := fun v hv w hw hvC hwC => by
        obtain ⟨k, hk'⟩ := htr v hv w hw (fun h' => hvC ⟨hVZ hv, h'⟩)
          (fun h' => hwC ⟨hVZ hw, h'⟩)
        refine ⟨k, hVZ ?_, hk'⟩
        exact V₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hd₀V₁ k) v).mp hv)
          (V₁.inv_mem hw)
      three := ⟨v₀, hv₀, w₀, hw₀, hnotC v₀ hv₀ hv₀C, hnotC w₀ hw₀ hw₀C,
        fun h' => hvw₀ h'.2⟩
      TI := fun y hy hW => (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hNC y hy
        (mem_normalizer_of_inf_ne_bot h4213 h1104 hG2 h331 h1102 h hk hVM hZC2 inf_le_right hW))
      norm := fun y hy hyC => by
        have hyM := hNZC ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr hyC)
        have hyV := hMV hyM
        have hgL : y * d₀ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyM d₀).mp hd₀L
        have hgV : y * d₀ * y⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hyV hd₀V) (Subgroup.inv_mem _ hyV)
        have hyV₁ := hV1n y hy hyV
        have hgV₁ : y * d₀ * y⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hyV₁ hd₀V₁) (Subgroup.inv_mem _ hyV₁)
        obtain ⟨k, hk'⟩ := hgen _ hgL hgV hgV₁
        have hpV : y * d₀ * y⁻¹ * (d₀ ^ k)⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) :=
          Subgroup.mul_mem _ hgV (Subgroup.inv_mem _ (Subgroup.pow_mem _ hd₀V k))
        have hp : conjV (fsuV T I) (y * d₀ * y⁻¹ * (d₀ ^ k)⁻¹) hpV ∈
            perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I))) := by
          convert hk' using 1
          ext v
          rw [MulAut.mul_apply, conjV_apply_coe, conjV_apply_coe, ← conjV_pow, ← conjV_inv,
            conjV_apply_coe]
          group
        have hpz := hcz _ (L.mul_mem hgL (L.inv_mem (L.pow_mem hd₀L k))) hpV hp
        refine ⟨k, fun z hz => ?_⟩
        have hz' : d₀ ^ k * z * (d₀ ^ k)⁻¹ ∈ omegaOneCenterOf (ROf T L V₁) :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hYZ hd₀R) k) z).mp hz
        have h1 := Subgroup.mem_centralizer_iff.mp hpz _ hz'
        calc y * d₀ * y⁻¹ * z * (y * d₀ * y⁻¹)⁻¹ =
            (y * d₀ * y⁻¹ * (d₀ ^ k)⁻¹) * (d₀ ^ k * z * (d₀ ^ k)⁻¹) *
              (y * d₀ * y⁻¹ * (d₀ ^ k)⁻¹)⁻¹ := by group
          _ = (d₀ ^ k * z * (d₀ ^ k)⁻¹) * (y * d₀ * y⁻¹ * (d₀ ^ k)⁻¹) *
              (y * d₀ * y⁻¹ * (d₀ ^ k)⁻¹)⁻¹ := by rw [← h1]
          _ = d₀ ^ k * z * (d₀ ^ k)⁻¹ := by group
      TC := fun t ht => hNC t (hTR ht) (h.normal ht) }
  rcases D.dichotomy with hY | hT'
  · exact hNot (hY.trans hNZC)
  · exact hNot (normalizer_le_of_centralizer h331 h hYZ hT' inf_le_left hNZC)

end CFSG.Quasithin.Vol2.Ch11.SecA
