module

public import CFSG.Quasithin.EmptyFaithful.T1531Geom
public import CFSG.Quasithin.EmptyFaithful.T1531Stage2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Res15346Easy {G : Type} [Group G] (T M V₁ V₂ : Subgroup G) : Prop where
  fusion : ∀ x ∈ VZ T M, ∀ g : G, g * x * g⁻¹ ∈ VZ T M →
    ∃ m ∈ M, m * x * m⁻¹ = g * x * g⁻¹
  totSingular_inter : ∀ g : G, g ∉ M →
    IsTotSingular153 T M V₁ V₂ (VZ T M ⊓ conjSubgroup (VZ T M) g)
  totSingular_of_normalizer : ∀ U : Subgroup G, U ≤ VZ T M → ⊥ < U → U < VZ T M →
    ¬ Subgroup.normalizer (U : Set G) ≤ M → IsTotSingular153 T M V₁ V₂ U
  one_lt_r : 1 < E3.rParam (VZ T M)
  normalizer_ZS : Subgroup.normalizer (ZS153 T M V₁ : Set G) ≤ M
  centralizer_nonsingular : ∀ v : G, v ≠ 1 → (v ∈ V₁ ∨ v ∈ V₂) →
    Subgroup.centralizer ({v} : Set G) ≤ M

@[expose] def Res15346W0 {G : Type} [Group G] (T M : Subgroup G) : Prop :=
  E3.wClos (VZ T M) 0 T ≤ Subgroup.centralizer (VZ T M : Set G)

@[expose] def Stage15346Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346Easy T M V₁ V₂ → Res15346W0 T M

section Easy

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem res15346Easy (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) :
    Res15346Easy T M V₁ V₂ where
  fusion := fusion_153 c.hyp c.decomp r45.centralizer₁
  totSingular_inter := fun _ hg => totSingular_inter_153 c.hyp c.decomp r45.centralizer₁ hg
  totSingular_of_normalizer := fun _ hUV _ _ hN =>
    totSingular_of_normalizer_153 c.hyp c.decomp r45.centralizer₁ hUV hN
  one_lt_r := one_lt_rParam_153 c.hyp c.decomp r45.centralizer₁
  normalizer_ZS := normalizer_ZS_153 c.hyp c.decomp r45.centralizer₁
  centralizer_nonsingular := centralizer_nonsingular_153 c.hyp c.decomp r45.centralizer₁

end Easy

section FromW0

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

omit [Finite G] in
theorem wParam_pos_of_w0 (hw0 : E3.wClos (VZ T M) 0 T ≤ Subgroup.centralizer (VZ T M : Set G)) :
    0 < E3.wParam T (VZ T M) := by
  have h1 : (1 : ℕ∞) ≤ E3.wParam T (VZ T M) := by
    refine le_iInf₂ fun j hj => ?_
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hj (le_inf (E3.wClos_le 0 T) hw0)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
  exact lt_of_lt_of_le one_pos h1

theorem conj_le_centralizer_of_w0 (h : Hyp153 G T Mc M)
    (hw0 : E3.wClos (VZ T M) 0 T ≤ Subgroup.centralizer (VZ T M : Set G)) {g : G}
    (hg : conjSubgroup (VZ T M) g ≤ M) :
    conjSubgroup (VZ T M) g ≤ Subgroup.centralizer (VZ T M : Set G) := by
  have hP : IsPGroup 2 (conjSubgroup (VZ T M) g) :=
    E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian h.elemAbelian) g
  have hT' : IsSylowIn 2 T M := h.isSylowTwoOf
  obtain ⟨m, hm, hle⟩ := E3.exists_le_conj_of_isSylowIn hT' hg hP
  have hA : conjSubgroup (VZ T M) (g * m⁻¹) ≤ T := by
    have := E3.conjSubgroup_mono_left m⁻¹ hle
    rwa [E3.conjSubgroup_conj_inv, conjSubgroup_conjSubgroup] at this
  have hmem : conjSubgroup (VZ T M) (g * m⁻¹) ∈ E3.gammaSet (VZ T M) 0 T :=
    ⟨hA, g * m⁻¹, le_rfl, E3.mQuot_self _⟩
  have hAC : conjSubgroup (VZ T M) (g * m⁻¹) ≤ Subgroup.centralizer (VZ T M : Set G) :=
    (E3.le_wClos hmem).trans hw0
  have h1 := E3.conjSubgroup_mono_left m hAC
  rw [conjSubgroup_conjSubgroup, show g * m⁻¹ * m = g by group, E3.conjSubgroup_centralizer,
    conjSubgroup_eq_iff_mem_normalizer.2 (h.le_normalizer hm)] at h1
  exact h1

theorem T_le_normalizer_R (h : Hyp153 G T Mc M) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
  intro t ht
  rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer ht),
    conjSubgroup_eq_iff_mem_normalizer.2 (h.le_normalizer (h.T_le ht))]

theorem exists_factor_normalizer_R (h : Hyp153 G T Mc M) {m : G} (hm : m ∈ M) :
    ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G),
      ∃ x ∈ M ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G), m = c * x := by
  have hCn : ∀ n ∈ M, conjSubgroup (M ⊓ Subgroup.centralizer (VZ T M : Set G)) n =
      M ⊓ Subgroup.centralizer (VZ T M : Set G) := fun n hn => by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 (h.le_normalizer hn),
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hn)]
  have hRC : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf (inf_le_left.trans h.T_le) inf_le_right
  have hTC : T ⊓ (M ⊓ Subgroup.centralizer (VZ T M : Set G)) =
      T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (le_inf inf_le_left hRC)
  have hRsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer (VZ T M : Set G))
      (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal h.isSylowTwoOf (inf_le_left :
      M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ M)
      (fun n hn => conjSubgroup_eq_iff_mem_normalizer.1 (hCn n hn))
    rwa [hTC] at this
  have hP : conjSubgroup (T ⊓ Subgroup.centralizer (VZ T M : Set G)) m⁻¹ ≤
      M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    have := E3.conjSubgroup_mono_left m⁻¹ hRC
    rwa [hCn m⁻¹ (M.inv_mem hm)] at this
  have hPp : IsPGroup 2 (conjSubgroup (T ⊓ Subgroup.centralizer (VZ T M : Set G)) m⁻¹) :=
    E3.isPGroup_conjSubgroup hRsyl.2.1 m⁻¹
  have hRsyl' : IsSylowIn 2 (T ⊓ Subgroup.centralizer (VZ T M : Set G))
      (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := hRsyl
  obtain ⟨c, hcC, hle⟩ := E3.exists_le_conj_of_isSylowIn hRsyl' hP hPp
  have heq : conjSubgroup (T ⊓ Subgroup.centralizer (VZ T M : Set G)) m⁻¹ =
      conjSubgroup (T ⊓ Subgroup.centralizer (VZ T M : Set G)) c :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (by rw [E3.card_conjSubgroup, E3.card_conjSubgroup]))
  refine ⟨c⁻¹, Subgroup.inv_mem _ hcC, c * m, ⟨M.mul_mem hcC.1 hm, ?_⟩, by group⟩
  refine conjSubgroup_eq_iff_mem_normalizer.1 ?_
  rw [← conjSubgroup_conjSubgroup, ← heq, E3.conjSubgroup_inv_conj]

theorem autI_normalizer_R (h : Hyp153 G T Mc M) :
    autI h.elemAbelian (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) =
      autI h.elemAbelian M := by
  refine le_antisymm (autI_mono _ inf_le_left) fun φ hφ => ?_
  obtain ⟨g, hgM, rfl⟩ := (mem_autI h.elemAbelian).1 hφ
  obtain ⟨c, hc, x, hx, hgcx⟩ := exists_factor_normalizer_R h hgM
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer hx.1
  have hcN : c ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer hc.1
  have e : g = ⟨c, hcN⟩ * ⟨x, hxN⟩ := Subtype.ext hgcx
  have hc1 : convI h.elemAbelian ⟨c, hcN⟩ = 1 := (convI_eq_one_iff h.elemAbelian _).2 hc.2
  rw [e, map_mul, hc1, one_mul]
  exact convI_mem_autI h.elemAbelian hx hxN

theorem isUniqueM_normalizer_R (h : Hyp153 G T Mc M)
    (hR : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≠ ⊥) :
    IsUniqueM (Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) M := by
  have hX : IsUniqueM (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) M :=
    h.isUniqueM_of_autI_eq_M (le_inf h.T_le (T_le_normalizer_R h)) inf_le_left
      (autI_normalizer_R h)
  have hR2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :=
    h.isSylowTwoOf.2.1.to_le inf_le_left
  have hloc : IsTwoLocal (Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) := ⟨_, hR, hR2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'M : M' = M := hX.2 M' ⟨hM', inf_le_right.trans hle⟩
  refine ⟨⟨hX.1.1, hle.trans_eq hM'M⟩, fun M'' hM'' => hX.2 M'' ⟨hM''.1,
    inf_le_right.trans hM''.2⟩⟩

theorem normalizer_w0_of_w0 (h : Hyp153 G T Mc M)
    (hw0 : E3.wClos (VZ T M) 0 T ≤ Subgroup.centralizer (VZ T M : Set G)) :
    Subgroup.normalizer (E3.wClos (VZ T M) 0 T : Set G) ≤ M := by
  have hV := h.elemAbelian
  have hWR : E3.wClos (VZ T M) 0 T ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf (E3.wClos_le 0 T) hw0
  have hrk : 0 < rk ↥(VZ T M) := by
    have h1 := card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
    rw [h.card_VZ] at h1
    by_contra hz
    have h0 : rk ↥(VZ T M) = 0 := by omega
    rw [h0] at h1
    norm_num at h1
  have hW1 : E3.wClos (VZ T M) 0 T ≠ ⊥ := E3.wClos_ne_bot hV h.VZ_le_T hrk
  have hR1 : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≠ ⊥ := fun e =>
    hW1 (le_bot_iff.mp (e ▸ hWR))
  have hR2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :=
    h.isSylowTwoOf.2.1.to_le inf_le_left
  have hT' : IsSylowIn 2 T M := h.isSylowTwoOf
  exact (E3.e3_16_one hT' (inf_le_left.trans h.T_le) hR2 hWR hW1
    (isUniqueM_normalizer_R h hR1)).2

end FromW0

theorem stage15346_of_four (i : Stage15346Four) : Stage15346 := by
  intro G _ _ T Mc M V₁ V₂ t c r45
  have e := res15346Easy c r45
  have w := i G T Mc M V₁ V₂ t c r45 e
  exact
    { fusion := e.fusion
      totSingular_inter := e.totSingular_inter
      totSingular_of_normalizer := e.totSingular_of_normalizer
      one_lt_r := e.one_lt_r
      w0_centralizes := w
      w_pos := wParam_pos_of_w0 w
      conj_le_centralizer := fun _ hg => conj_le_centralizer_of_w0 c.hyp w hg
      normalizer_w0 := normalizer_w0_of_w0 c.hyp w
      normalizer_ZS := e.normalizer_ZS
      centralizer_nonsingular := e.centralizer_nonsingular }

end CFSG.Quasithin
