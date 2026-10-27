module

public import CFSG.Quasithin.H13.L32NLem14332h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjAct_coe {V : Subgroup G} (c : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAct V c v : ↥V) : G) = c * v * (c : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl c) v

theorem mem_normalizer_of_maps {X : Subgroup G} {c : G} (h : ∀ w ∈ X, c * w * c⁻¹ ∈ X) :
    c ∈ Subgroup.normalizer (X : Set G) := by
  let f : ↥X → ↥X := fun w => ⟨c * (w : G) * c⁻¹, h w w.2⟩
  have hinj : Function.Injective f := by
    intro u w huw
    apply Subtype.ext
    have h1 : c * (u : G) * c⁻¹ = c * (w : G) * c⁻¹ := congrArg Subtype.val huw
    simpa using h1
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨w, hw⟩ := hsurj ⟨c * y * c⁻¹, hy⟩
  have h1 : c * (w : G) * c⁻¹ = c * y * c⁻¹ := congrArg Subtype.val hw
  have h2 : (w : G) = y := by simpa using h1
  rw [← h2]
  exact w.2

structure Ctx (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g z b l : G)
    [IsMulCommutative ↥V] : Prop where
  hyp : Hyp14310One G T L V
  lt : fsuV1 T V < centerOf (fsuU T V)
  plane : IsL32NPlane T V V₂
  setting : Setting1282One G T L V 3 (fsuV1 T V) V₂
  gP : g ∈ p128 T L V
  gN : g ∉ l32nH T V
  S : L32NSet14.Setting G T L V V₂
  z_mem : z ∈ fsuV1 T V
  z_ne : z ≠ 1
  b_mem : b ∈ V
  b_nmem : b ∉ V₂
  l_mem : l ∈ L
  l3 : l ^ 3 = 1
  l_a : l * (g⁻¹ * z * g) * l⁻¹ = g⁻¹ * z * g
  l_z : l * z * l⁻¹ = b
  l_b : l * b * l⁻¹ = z * b
  U_T : fsuU T V ≤ T
  T_U : T ≤ Subgroup.normalizer (fsuU T V : Set G)
  zI : centerOf (i128 T L V (fsuV1 T V)) =
    centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g
  I_eq : i128 T L V (fsuV1 T V) = oTwoUpper (p128 T L V) ⊔ fsuU T V

variable {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem g_mem_normalizer {g : G} (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) :
    g ∈ Subgroup.normalizer (V₂ : Set G) :=
  L128P.p128_le_normalizer le_rfl hV₂.1 hgP

theorem conj_z_mem {g z : G} (S : L32NSet14.Setting G T L V V₂) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V) (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) :
    g⁻¹ * z * g ∈ V₂ ∧ g⁻¹ * z * g ∉ fsuV1 T V := by
  have hgV₂ := g_mem_normalizer hV₂ hgP
  refine ⟨?_, fun ha => ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgV₂) z).mp
      (hV₂.2 hz)
    simpa using this
  · rcases S.eq_of_mem_V1 hz hz1 ha with h1 | h1
    · apply hz1
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · apply hgN
      refine S.mem_g1 hz hz1 ?_
      calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
        _ = z := by group

theorem exists_ctx (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12810 : Lemma12_8_10) {T L V : Subgroup G}
    (h : Hyp14310One G T L V) (hlt : fsuV1 T V < centerOf (fsuU T V)) :
    ∃ _ : IsMulCommutative ↥V, ∃ (V₂ : Subgroup G) (g z b l : G), Ctx G T L V V₂ g z b l := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨hc, S⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis
  obtain ⟨haV₂, ha1⟩ := conj_z_mem S hV₂ hgP hgN hz hz1
  have hzV₂ : z ∈ V₂ := hV₂.2 hz
  have hzV : z ∈ V := hV₂.1.1 hzV₂
  have haV : g⁻¹ * z * g ∈ V := hV₂.1.1 haV₂
  obtain ⟨l, hlL, hl3, hla, hlz, hlb⟩ := S.exists_rot haV hzV hbV hz1
    (fun h1 => hbV₂ (h1 ▸ one_mem _)) (fun h1 => ha1 (h1 ▸ hz)) (fun h1 => hbV₂ (h1 ▸ haV₂))
    (fun h1 => hbV₂ (h1 ▸ hzV₂)) (fun h1 => hbV₂ (h1 ▸ V₂.mul_mem haV₂ hzV₂))
  obtain ⟨hUT, hTU⟩ := (hs.almostSpecial h1222 h12213).G22_three
  exact ⟨hc, V₂, g, z, b, l, ⟨h, hlt, hV₂, hs, hgP, hgN, S, hz, hz1, hbV, hbV₂, hlL, hl3, hla,
    hlz, hlb, hUT, hTU, (h12810 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.1.symm,
    L128P.i128_eq_sup h1222 h12213 hs⟩⟩

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l)
include C

theorem a_mem : g⁻¹ * z * g ∈ V₂ :=
  (conj_z_mem C.S C.plane C.gP C.gN C.z_mem C.z_ne).1

theorem a_nmem : g⁻¹ * z * g ∉ fsuV1 T V :=
  (conj_z_mem C.S C.plane C.gP C.gN C.z_mem C.z_ne).2

theorem z_V₂ : z ∈ V₂ := C.plane.2 C.z_mem

theorem z_V : z ∈ V := C.plane.1.1 C.z_V₂

theorem a_V : g⁻¹ * z * g ∈ V := C.plane.1.1 C.a_mem

@[expose] def zz : ↥V := ⟨z, C.z_V⟩

@[expose] def aa : ↥V := ⟨g⁻¹ * z * g, C.a_V⟩

@[expose] def bb : ↥V := ⟨b, C.b_mem⟩

theorem sq_V (v : ↥V) : v * v = 1 := Subtype.ext (C.S.mul_self_V v.2)

theorem sq_V' (v w : ↥V) : v * (v * w) = w := by rw [← mul_assoc, C.sq_V, one_mul]

theorem mulAut_eq_one {φ : MulAut ↥V} (hz : φ C.zz = C.zz) (ha : φ C.aa = C.aa)
    (hb : φ C.bb = C.bb) : φ = 1 := by
  have S := C.S
  have h1 : ∀ (w : G) (hw : w ∈ fsuV1 T V), φ ⟨w, (Subgroup.mem_inf.mp hw).1⟩ =
      ⟨w, (Subgroup.mem_inf.mp hw).1⟩ := by
    intro w hw
    rcases S.eq_of_mem_V1 C.z_mem C.z_ne hw with rfl | rfl
    · exact map_one φ
    · exact hz
  have h2 : ∀ (w : G) (hw : w ∈ V₂), φ ⟨w, C.plane.1.1 hw⟩ = ⟨w, C.plane.1.1 hw⟩ := by
    intro w hw
    rcases S.mem_V2 C.a_mem C.a_nmem hw with h | h
    · exact h1 w h
    · have e : (⟨w, C.plane.1.1 hw⟩ : ↥V) =
          C.aa⁻¹ * ⟨g⁻¹ * z * g * w, (Subgroup.mem_inf.mp h).1⟩ :=
        Subtype.ext (by simp only [aa, Subgroup.coe_mul, Subgroup.coe_inv]; group)
      rw [e, map_mul, map_inv, ha, h1 _ h]
  ext ⟨v, hv⟩
  rcases S.mem_V C.b_mem C.b_nmem hv with h | h
  · exact congrArg Subtype.val (h2 v h)
  · have e : (⟨v, hv⟩ : ↥V) = C.bb⁻¹ * ⟨b * v, C.plane.1.1 h⟩ :=
      Subtype.ext (by simp [bb])
    rw [e, map_mul, map_inv, hb, h2 _ h]
    rfl

theorem mulAut_eq {φ ψ : MulAut ↥V} (hz : φ C.zz = ψ C.zz) (ha : φ C.aa = ψ C.aa)
    (hb : φ C.bb = ψ C.bb) : φ = ψ := by
  have h := C.mulAut_eq_one (φ := ψ⁻¹ * φ) (by rw [MulAut.mul_apply, hz, MulAut.inv_apply_self])
    (by rw [MulAut.mul_apply, ha, MulAut.inv_apply_self])
    (by rw [MulAut.mul_apply, hb, MulAut.inv_apply_self])
  rw [← mul_inv_cancel_left ψ φ, h, mul_one]

end Ctx

end L14328

end CFSG.Quasithin.H13
