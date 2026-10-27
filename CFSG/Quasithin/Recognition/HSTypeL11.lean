module

public import CFSG.Quasithin.Recognition.HSTypeSetting
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.G2
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem card_autOn_le_of_centralizes [Finite G] {Y V W : Subgroup G}
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hYW : Y ≤ Subgroup.centralizer (W : Set G))
    (hidx : (W.subgroupOf V).index = 2) :
    Nat.card (autOn Y V) ≤ Nat.card W := by
  obtain ⟨v, hvW⟩ : ∃ v : ↥V, v ∉ W.subgroupOf V := by
    by_contra hne
    push Not at hne
    have htop : W.subgroupOf V = ⊤ := eq_top_iff.mpr fun x _ => hne x
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hfix : ∀ α ∈ autOn Y V, ∀ w : ↥V, (w : G) ∈ W → α w = w := by
    intro α hα w hw
    obtain ⟨y, rfl⟩ := (mem_autOn_iff hYV).mp hα
    apply Subtype.ext
    rw [actionOn_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp (hYW y.2) w hw
    rw [← this, mul_inv_cancel_right]
  have hmem : ∀ α ∈ autOn Y V, ((v⁻¹ * α v : ↥V) : G) ∈ W := by
    intro α hα
    have hαv : α v ∉ W.subgroupOf V := by
      intro hin
      apply hvW
      have h1 := hfix α hα (α v) hin
      rwa [α.injective h1] at hin
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := v⁻¹) (b := α v)).mpr
      ⟨fun h => absurd (by simpa using (W.subgroupOf V).inv_mem h) hvW,
        fun h => absurd h hαv⟩
    exact this
  let f : ↥(autOn Y V) → ↥W := fun α => ⟨_, hmem α α.2⟩
  have hf : Function.Injective f := by
    intro α β hαβ
    have hv : α.1 v = β.1 v := by
      have := congrArg Subtype.val hαβ
      simp only [f] at this
      have h2 : v⁻¹ * α.1 v = v⁻¹ * β.1 v := Subtype.ext this
      exact mul_left_cancel h2
    apply Subtype.ext
    refine MulEquiv.ext fun x => ?_
    by_cases hx : x ∈ W.subgroupOf V
    · rw [hfix α.1 α.2 x hx, hfix β.1 β.2 x hx]
    · have hvx : v⁻¹ * x ∈ W.subgroupOf V :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr
          ⟨fun h => absurd (by simpa using (W.subgroupOf V).inv_mem h) hvW,
            fun h => absurd h hx⟩
      calc α.1 x = α.1 (v * (v⁻¹ * x)) := by rw [mul_inv_cancel_left]
        _ = α.1 v * α.1 (v⁻¹ * x) := map_mul _ _ _
        _ = β.1 v * β.1 (v⁻¹ * x) := by
          rw [hfix α.1 α.2 (v⁻¹ * x) hvx, hfix β.1 β.2 (v⁻¹ * x) hvx, hv]
        _ = β.1 (v * (v⁻¹ * x)) := (map_mul _ _ _).symm
        _ = β.1 x := by rw [mul_inv_cancel_left]
  exact Nat.card_le_card_of_injective f hf

theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hz]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    simp [hk]
  · right
    simp [hk]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem card_autOn_M [Finite G] (h : HSSetting z V) : Nat.card (autOn (hsM V) V) = 168 := by
  rw [card_autOn_eq_relIndex (le_refl (hsM V)), h.centralizer_V_eq]
  have h1 := Subgroup.relIndex_mul_card (hsP V) (hsM V)
  rw [inf_eq_left.mpr h.P_le_M, h.card_P, h.card_M] at h1
  omega

theorem card_mulAut_V [Finite G] (h : HSSetting z V) : Nat.card (MulAut V) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 3)
    (W := ↥V) (fun a b => h.elem.1.is_comm.comm a b)
    (fun a => Subtype.ext (h.elem.2 a a.2)) (by rw [h.card_V]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide

theorem autOn_M_eq_top [Finite G] (h : HSSetting z V) : autOn (hsM V) V = ⊤ :=
  Subgroup.eq_top_of_card_eq _ (by rw [h.card_autOn_M, h.card_mulAut_V])

variable {T : Subgroup G}

theorem card_T [Finite G] (h : HSSetting z V) (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    Nat.card T = 512 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
  have h1 := Subgroup.card_mul_index (T.subgroupOf (hsH z ⊓ hsM V))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv, hk, h.card_H_inf_M] at h1
  have hodd := hT.2.2
  have hpos : 0 < (T.subgroupOf (hsH z ⊓ hsM V)).index :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0] at h1; simp at h1
  have hk10 : k ≤ 10 := by
    by_contra hk10
    have : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  rw [hk]
  interval_cases k <;> omega

theorem isSylowTwoOf_M [Finite G] (h : HSSetting z V) (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    IsSylowTwoOf T (hsM V) := by
  refine ⟨hT.1.trans inf_le_right, hT.2.1, fun hd => ?_⟩
  have h1 := Subgroup.card_mul_index (T.subgroupOf (hsM V))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT.1.trans inf_le_right)).toEquiv,
    h.card_T hT, h.card_M] at h1
  obtain ⟨c, hc⟩ := hd
  omega

theorem isSylowTwoOf_H [Finite G] (h : HSSetting z V) (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    IsSylowTwoOf T (hsH z) := by
  refine ⟨hT.1.trans inf_le_left, hT.2.1, fun hd => ?_⟩
  have h1 := Subgroup.card_mul_index (T.subgroupOf (hsH z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT.1.trans inf_le_left)).toEquiv,
    h.card_T hT, h.card_H] at h1
  obtain ⟨c, hc⟩ := hd
  omega

theorem P_le_T [Finite G] (h : HSSetting z V) (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    hsP V ≤ T := by
  rw [h.P_eq_pCoreOf]
  exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf (h.isSylowTwoOf_M hT)

theorem z_mem_T [Finite G] (h : HSSetting z V) (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) : z ∈ T :=
  h.P_le_T hT (h.V_le_P h.mem_V)

theorem inf_centralizer_T_eq [Finite G] (h : HSSetting z V)
    (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    V ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z := by
  set C := V ⊓ Subgroup.centralizer (T : Set G) with hC
  have hzC : z ∈ C := ⟨h.mem_V, Subgroup.mem_centralizer_iff.mpr fun t ht =>
    (Subgroup.mem_centralizer_singleton_iff.mp ((hT.1.trans inf_le_left) ht))⟩
  have hTM : T ≤ hsM V := hT.1.trans inf_le_right
  have hCdvd : Nat.card C ∣ 8 := h.card_V ▸ Subgroup.card_dvd_of_le inf_le_left
  have hTc := h.card_T hT
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, h.orderOf_z]
  have hzle : Subgroup.zpowers z ≤ C := (Subgroup.zpowers_le).mpr hzC
  have hC2 : 2 ≤ Nat.card C := hz2 ▸ Subgroup.card_le_of_le hzle
  have hcases : Nat.card C = 2 ∨ Nat.card C = 4 ∨ Nat.card C = 8 := by
    have h8 : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hCdvd
    interval_cases hc : Nat.card C <;> simp_all
  rcases hcases with h2 | h4 | h8
  · exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [h2, hz2])).symm
  · exfalso
    have hidx : (C.subgroupOf V).index = 2 := by
      have h1 := Subgroup.card_mul_index (C.subgroupOf V)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h4, h.card_V] at h1
      omega
    have hTC : T ≤ Subgroup.centralizer (C : Set G) :=
      Subgroup.le_centralizer_iff.mp (inf_le_right : C ≤ Subgroup.centralizer (T : Set G))
    have hle := card_autOn_le_of_centralizes hTM hTC hidx
    have hTcard := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer (V : Set G)) T
    rw [← card_autOn_eq_relIndex hTM] at hTcard
    have hTP : T ⊓ Subgroup.centralizer (V : Set G) ⊓ T ≤ hsP V := by
      rw [← h.centralizer_V_eq]
      exact fun x hx => ⟨hTM hx.2, hx.1.2⟩
    have hPc := Subgroup.card_le_of_le hTP
    rw [h.card_P] at hPc
    rw [hTc] at hTcard
    rw [h4] at hle
    have := Nat.mul_le_mul hle hPc
    omega
  · exfalso
    have hCV : C = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.card_V])
    have hVT : V ≤ Subgroup.centralizer (T : Set G) := hCV ▸ inf_le_right
    have hTP : T ≤ hsP V := by
      rw [← h.centralizer_V_eq]
      exact le_inf hTM (Subgroup.le_centralizer_iff.mp hVT)
    have := Subgroup.card_le_of_le hTP
    rw [hTc, h.card_P] at this
    omega

theorem eq_z_of_mem_center_T [Finite G] (h : HSSetting z V)
    (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) {x : G} (hxT : x ∈ T)
    (hxc : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = z := by
  have hTM : T ≤ hsM V := hT.1.trans inf_le_right
  have hxP : x ∈ hsP V := by
    refine centralizer_quasithinGenFitting_le (hsM V) ⟨hTM hxT, ?_⟩
    exact Subgroup.centralizer_le (by exact_mod_cast h.P_le_T hT) hxc
  have hxV : x ∈ V := h.mem_V_of_mem_P hxP hx2
  have hxz : x ∈ Subgroup.zpowers z := h.inf_centralizer_T_eq hT ▸ ⟨hxV, hxc⟩
  exact (eq_one_or_eq_of_mem_zpowers h.orderOf_z hxz).resolve_left hx1

theorem normalizer_T_le_H [Finite G] (h : HSSetting z V)
    (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    Subgroup.normalizer (T : Set G) ≤ hsH z := by
  intro g hg
  have hzT := h.z_mem_T hT
  have hgz : g * z * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg z).mp hzT
  have hgzc : g * z * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : g⁻¹ * t * g ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
      simpa using this
    have hc : g⁻¹ * t * g * z = z * (g⁻¹ * t * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp ((hT.1.trans inf_le_left) ht')
    calc t * (g * z * g⁻¹) = g * (g⁻¹ * t * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * t := by group
  have hgz2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
  have hgz1 : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply h.z_ne_one
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h1]
    group
  have := h.eq_z_of_mem_center_T hT hgz hgzc hgz2 hgz1
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [this]

theorem isSylowTwo_T [Finite G] (h : HSSetting z V) (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) :
    quasithinIsSylowTwo T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hT.2.1, fun hd => ?_⟩
  have hTc : Nat.card T = 2 ^ 9 := by rw [h.card_T hT]; norm_num
  have hG : 2 ^ (9 + 1) ∣ Nat.card G := by
    rw [← T.card_mul_index, hTc, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have hN := Sylow.prime_pow_dvd_card_normalizer hG hTc
  have hNH := Subgroup.card_dvd_of_le (h.normalizer_T_le_H hT)
  rw [h.card_H] at hNH
  have := hN.trans hNH
  norm_num at this

end HSSetting

end CFSG.Quasithin.HSType
